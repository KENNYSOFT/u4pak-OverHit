#!/usr/bin/env python
# coding=UTF-8
#
# Copyright (c) 2014 Mathias Panzenböck
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

from __future__ import with_statement, division, print_function

import os
import sys
import hashlib
import zlib
import math

from struct import unpack as st_unpack, pack as st_pack
from collections import OrderedDict, namedtuple
from io import DEFAULT_BUFFER_SIZE
from binascii import hexlify
from Crypto.Cipher import AES

HAS_STAT_NS = hasattr(os.stat_result, 'st_atime_ns')

__all__ = 'read_index', 'pack'

# for Python 2/3 compatibility:
try:
	xrange
except NameError:
	xrange = range

try:
	buffer
except NameError:
	buffer = memoryview

try:
	itervalues = dict.itervalues
except AttributeError:
	itervalues = dict.values

# for Python < 3.3 and Windows
def highlevel_sendfile(outfile,infile,offset,size):
	infile.seek(offset,0)
	buf_size = DEFAULT_BUFFER_SIZE
	buf = bytearray(buf_size)
	while size > 0:
		if size >= buf_size:
			n = infile.readinto(buf)
			if n < buf_size:
				raise IOError("unexpected end of file")
			outfile.write(buf)
			size -= buf_size
		else:
			data = infile.read(size)
			if len(data) < size:
				raise IOError("unexpected end of file")
			outfile.write(data)
			size = 0

if hasattr(os, 'sendfile'):
	def sendfile(outfile,infile,offset,size):
		try:
			out_fd = outfile.fileno()
			in_fd  = infile.fileno()
		except:
			highlevel_sendfile(outfile,infile,offset,size)
		else:
			# size == 0 has special meaning for some sendfile implentations
			if size > 0:
				os.sendfile(out_fd, in_fd, offset, size)
else:
	sendfile = highlevel_sendfile

def raise_check_error(ctx, message):
	if ctx is None:
		raise ValueError(message)

	elif isinstance(ctx, Record):
		raise ValueError("%s: %s" % (ctx.filename, message))

	else:
		raise ValueError("%s: %s" % (ctx, message))

class FragInfo(object):
	__slots__ = ('__frags','__size')

	def __init__(self,size,frags=None):
		self.__size  = size
		self.__frags = []
		if frags:
			for start, end in frags:
				self.add(start, end)

	@property
	def size(self):
		return self.__size

	def __iter__(self):
		return iter(self.__frags)

	def __len__(self):
		return len(self.__frags)

	def __repr__(self):
		return 'FragInfo(%r,%r)' % (self.__size, self.__frags)

	def add(self,new_start,new_end):
		if new_start >= new_end:
			return

		elif new_start >= self.__size or new_end > self.__size:
			raise IndexError("range out of bounds: (%r, %r]" % (new_start, new_end))

		frags = self.__frags
		for i, (start, end) in enumerate(frags):
			if new_end < start:
				frags.insert(i, (new_start, new_end))
				return

			elif new_start <= start:
				if new_end <= end:
					frags[i] = (new_start, end)
					return

			elif new_start <= end:
				if new_end > end:
					new_start = start
			else:
				continue

			j = i+1
			n = len(frags)
			while j < n:
				next_start, next_end = frags[j]
				if next_start <= new_end:
					j += 1
					if next_end > new_end:
						new_end = next_end
						break
				else:
					break

			frags[i:j] = [(new_start, new_end)]
			return

		frags.append((new_start, new_end))

	def invert(self):
		inverted = FragInfo(self.__size)
		append   = inverted.__frags.append
		prev_end = 0

		for start, end in self.__frags:
			if start > prev_end:
				append((prev_end, start))
			prev_end = end

		if self.__size > prev_end:
			append((prev_end, self.__size))

		return inverted

	def free(self):
		free     = 0
		prev_end = 0

		for start, end in self.__frags:
			free += start - prev_end
			prev_end = end

		free += self.__size - prev_end

		return free

class Pak(object):
	__slots__ = ('version', 'index_offset', 'index_size', 'footer_offset', 'index_sha1', 'mount_point', 'records')

	def __init__(self,version,index_offset,index_size,footer_offset,index_sha1,mount_point=None,records=None):
		self.version       = version
		self.index_offset  = index_offset
		self.index_size    = index_size
		self.footer_offset = footer_offset
		self.index_sha1    = index_sha1
		self.mount_point   = mount_point
		self.records       = records or []

	def __len__(self):
		return len(self.records)

	def __iter__(self):
		return iter(self.records)

	def __repr__(self):
		return 'Pak(version=%r, index_offset=%r, index_size=%r, footer_offset=%r, index_sha1=%r, mount_point=%r, records=%r)' % (
			self.version, self.index_offset, self.index_size, self.footer_offset, self.index_sha1, self.mount_point, self.records)

	def check_integrity(self,stream,callback=raise_check_error):
		index_offset = self.index_offset
		buf = bytearray(DEFAULT_BUFFER_SIZE)

		if self.version == 4:
			read_record = read_record_v4

		def check_data(ctx, offset, size, sha1):
			hasher = hashlib.sha1()
			stream.seek(offset, 0)

			while size > 0:
				if size >= DEFAULT_BUFFER_SIZE:
					size -= stream.readinto(buf)
					hasher.update(buf)
				else:
					rest = stream.read(size)
					hasher.update(rest)
					size = 0

			if hasher.digest() != sha1:
				callback(ctx,
						 'checksum missmatch:\n'
						 '\tgot:      %s\n'
						 '\texpected: %s' % (
							 hasher.hexdigest(),
							 hexlify(sha1).decode('latin1')))

		def check_original_data(ctx, offset, size, original_sha1):
			hasher = hashlib.sha1()
			stream.seek(offset, 0)

			buf = stream.read(size)
			if ctx.encrypted:
				buf = AES.new("E1A1F2E4AA066C54BD5090F463EDDF58".encode(), AES.MODE_ECB).decrypt(buf)[:ctx.compressed_size]
			if ctx.compression_method == COMPR_ZLIB:
				for block in ctx.compression_blocks:
					block_offset = block[0] - ctx.data_offset
					block_size = block[1] - block[0]
					block_content = buf[block_offset:block_offset+block_size]
					block_decompress = zlib.decompress(block_content)
					hasher.update(block_decompress)
			else:
				hasher.update(buf)

			if hasher.digest() != original_sha1:
				callback(ctx,
						 'checksum missmatch:\n'
						 '\tgot:      %s\n'
						 '\texpected: %s' % (
							 hasher.hexdigest(),
							 hexlify(original_sha1).decode('latin1')))

		# test index sha1 sum
		check_data("<archive index>", index_offset, self.index_size, self.index_sha1)

		for r1 in self:
			stream.seek(r1.offset, 0)
			r2 = read_record(stream, r1.filename)

			# test index metadata
			if not same_metadata(r1, r2):
				callback(r1, 'metadata missmatch:\n%s' % metadata_diff(r1, r2))

			if r1.compression_method not in COMPR_METHODS:
				callback(r1, 'unknown compression method: 0x%02x' % r1.compression_method)

			if r1.compression_method == COMPR_NONE and r1.compressed_size != r1.uncompressed_size:
				callback(r1, 'file is not compressed but compressed size (%d) differes from uncompressed size (%d)' %
						 (r1.compressed_size, r1.uncompressed_size))

			if r1.data_offset + r1.compressed_size > index_offset:
				callback('data bleeds into index')

			# test file sha1 sum
			# XXX: I don't know if the sha1 is of the comressed (and encrypted) data
			#      or if it would need to uncompress (and decrypt) the data first.
			check_data(r1, r1.data_offset, r1.data_size, r1.sha1)
			if r1.compression_method != COMPR_NONE or r1.encrypted:
				check_original_data(r1, r1.data_offset, r1.data_size, r1.original_sha1)

	def unpack(self,stream,outdir=".",callback=lambda name: None):
		for record in self:
			record.unpack(stream,outdir,callback)

	def unpack_only(self,stream,files,outdir=".",callback=lambda name: None):
		for record in self:
			if shall_unpack(files,record.filename):
				record.unpack(stream,outdir,callback)

	def frag_info(self):
		frags = FragInfo(self.footer_offset + 52)
		frags.add(self.index_offset, self.index_offset + self.index_size)
		frags.add(self.footer_offset, frags.size)

		for record in self.records:
			frags.add(record.offset, record.data_offset + record.data_size)

		return frags

	def print_list(self,details=False,human=False,delim="\n",sort_key_func=None,out=sys.stdout):
		records = self.records

		if sort_key_func:
			records = sorted(records,key=sort_key_func)

		if details:
			if human:
				size_to_str = human_size
			else:
				size_to_str = str

			count = 0
			sum_size = 0
			out.write("    Offset        Size  Compr-Method  Compr-Size  Original SHA1                             SHA1                                      Name%s" % delim)
			for record in records:
				size  = size_to_str(record.uncompressed_size)
				sha1  = hexlify(record.sha1).decode('latin1')
				osha1 = hexlify(record.original_sha1).decode('latin1')
				cmeth = record.compression_method

				if cmeth == COMPR_NONE:
					out.write("%10u  %10s             -           -  %s  %s  %s%s" % (
						record.data_offset, size, osha1, sha1, record.filename, delim))
				else:
					out.write("%10u  %10s  %12s  %10s  %s  %s  %s%s" % (
						record.data_offset, size, COMPR_METHOD_NAMES[cmeth],
						size_to_str(record.compressed_size), osha1, sha1,
						record.filename, delim))
				count += 1
				sum_size += record.uncompressed_size
			out.write("%d file(s) (%s) %s" % (count, size_to_str(sum_size), delim))
		else:
			for record in records:
				out.write("%s%s" % (record.filename, delim))

	def print_info(self,human=False,out=sys.stdout):
		if human:
			size_to_str = human_size
		else:
			size_to_str = str

		csize = 0
		size  = 0
		for record in self.records:
			csize += record.compressed_size
			size  += record.uncompressed_size

		frags = self.frag_info()

		out.write("Pak Version: %d\n" % self.version)
		out.write("Index SHA1:  %s\n" % hexlify(self.index_sha1).decode('latin1'))
		out.write("Mount Point: %s\n" % self.mount_point)
		out.write("File Count:  %d\n" % len(self.records))
		out.write("Archive Size:            %10s\n" % size_to_str(frags.size))
		out.write("Unallocated Bytes:       %10s\n" % size_to_str(frags.free()))
		out.write("Sum Compr. Files Size:   %10s\n" % size_to_str(csize))
		out.write("Sum Uncompr. Files Size: %10s\n" % size_to_str(size))
		out.write("\n")
		out.write("Fragments (%d):\n" % len(frags))

		for start, end in frags:
			out.write("\t%10s ... %10s (%10s)\n" % (start, end, size_to_str(end - start)))

# compare all metadata except for the filename
def same_metadata(r1,r2):
	# data records always have offset == 0 it seems, so skip that
	return \
		r1.compressed_size        == r2.compressed_size    and \
		r1.uncompressed_size      == r2.uncompressed_size  and \
		r1.compression_method     == r2.compression_method and \
		r1.timestamp              == r2.timestamp          and \
		r1.sha1                   == r2.sha1               and \
		r1.compression_blocks     == r2.compression_blocks and \
		r1.encrypted              == r2.encrypted          and \
		r1.compression_block_size == r2.compression_block_size

def metadata_diff(r1,r2):
	diff = []

	for attr in ['compressed_size', 'uncompressed_size', 'timestamp', 'encrypted', 'compression_block_size']:
		v1 = getattr(r1,attr)
		v2 = getattr(r2,attr)
		if v1 != v2:
			diff.append('\t%s: %r != %r' % (attr, v1, v2))

	if r1.sha1 != r2.sha1:
		diff.append('\tsha1: %s != %s' % (hexlify(r1.sha1).decode('latin1'), hexlify(r2.sha1).decode('latin1')))

	if r1.compression_blocks != r2.compression_blocks:
		diff.append('\tcompression_blocks:\n\t\t%r\n\t\t\t!=\n\t\t%r' % (r1.compression_blocks, r2.compression_blocks))

	return '\n'.join(diff)

COMPR_NONE        = 0x00
COMPR_ZLIB        = 0x01

COMPR_METHODS = {COMPR_NONE, COMPR_ZLIB}

COMPR_METHOD_NAMES = {
	COMPR_NONE: 'none',
	COMPR_ZLIB: 'zlib'
}

class Record(namedtuple('RecordBase', [
	'filename', 'offset', 'compressed_size', 'uncompressed_size', 'compression_method',
	'timestamp', 'original_sha1', 'sha1', 'compression_blocks', 'encrypted', 'compression_block_size'])):

	def sendfile(self,outfile,infile):
		if self.encrypted:
			infile.seek(self.data_offset)
			data_content = infile.read(self.data_size)
			data_decrypt = AES.new("E1A1F2E4AA066C54BD5090F463EDDF58".encode(), AES.MODE_ECB).decrypt(data_content)[:self.compressed_size]
		if self.compression_method == COMPR_NONE:
			if self.encrypted:
				outfile.write(data_decrypt)
				return
			sendfile(outfile, infile, self.data_offset, self.uncompressed_size)
		elif self.compression_method == COMPR_ZLIB:
			for block in self.compression_blocks:
				block_offset = block[0]
				block_size = block[1] - block[0]
				if self.encrypted:
					block_offset -= self.data_offset
					block_content = data_decrypt[block_offset:block_offset+block_size]
				else:
					infile.seek(block_offset)
					block_content = infile.read(block_size)
				block_decompress = zlib.decompress(block_content)
				outfile.write(block_decompress)
		else:
			raise NotImplementedError('decompression is not implemented yet')

	def unpack(self,stream,outdir=".",callback=lambda name: None):
		prefix, name = os.path.split(self.filename)
		prefix = os.path.join(outdir,prefix)
		if not os.path.exists(prefix):
			os.makedirs(prefix)
		name = os.path.join(prefix,name)
		callback(name)
		with open(name,"wb") as fp:
			self.sendfile(fp,stream)

	@property
	def data_offset(self):
		return self.offset + self.header_size

	@property
	def index_size(self):
		name_size = 4 + len(self.filename.replace(os.path.sep,'/').encode('utf-8')) + 1
		return name_size + self.header_size

	@property
	def header_size(self):
		raise NotImplementedError

	@property
	def data_size(self):
		return 16 * math.ceil(self.compressed_size / 16) if self.encrypted else self.compressed_size

class RecordV4(Record):
	def __new__(cls, filename, offset, compressed_size, uncompressed_size, compression_method, original_sha1, sha1,
				compression_blocks, encrypted, compression_block_size):
		return Record.__new__(cls, filename, offset, compressed_size, uncompressed_size,
							  compression_method, None, original_sha1, sha1, compression_blocks, encrypted,
							  compression_block_size)

	@property
	def header_size(self):
		size = 53
		if self.compression_method != COMPR_NONE:
			size += 4
			size += len(self.compression_blocks) * 16
		if self.encrypted:
			size += 20
		return size

def read_path(stream,encoding='utf-8'):
	path_len, = st_unpack('<I',stream.read(4))
	return stream.read(path_len).rstrip(b'\0').decode(encoding).replace('/',os.path.sep)

def read_record_v4(stream, filename):
	offset, compressed_size, uncompressed_size, compression_method, original_sha1, sha1 = \
		st_unpack('<QQQI20s20s', stream.read(68))

	# sys.stdout.write('compression_method = %s\n' % compression_method)
	if compression_method != COMPR_NONE:
		block_count, = st_unpack('<I', stream.read(4))
		blocks = st_unpack('<%dQ' % (block_count * 2), stream.read(16 * block_count))
		blocks = [(blocks[i], blocks[i + 1]) for i in xrange(0, block_count * 2, 2)]
	else:
		blocks = None

	encrypted, compression_block_size = st_unpack('<BI', stream.read(5))

	return RecordV4(filename, offset, compressed_size, uncompressed_size, compression_method,
					original_sha1, sha1, blocks, encrypted != 0, compression_block_size)

def read_index(stream,check_integrity=False,ignore_magic=False,encoding='utf-8',force_version=None):
	stream.seek(-52, 2)
	footer_offset = stream.tell()
	footer = stream.read(52)
	magic, version, patch_version, index_offset, index_size, index_sha1 = st_unpack('<IIQQQ20s',footer)

	if not ignore_magic and magic != 0x5A6F12E1:
		raise ValueError('illegal file magic: 0x%08x' % magic)

	if force_version is not None:
		version = force_version

	if version == 4:
		read_record = read_record_v4

	else:
		raise ValueError('unsupported version: %d' % version)

	if index_offset + index_size > footer_offset:
		raise ValueError('illegal index offset/size')

	stream.seek(index_offset, 0)

	mount_point = read_path(stream, encoding)
	entry_count = st_unpack('<I',stream.read(4))[0]

	pak = Pak(version, index_offset, index_size, footer_offset, index_sha1, mount_point)

	for i in xrange(entry_count):
		filename = read_path(stream, encoding)
		record   = read_record(stream, filename)
		pak.records.append(record)

	if stream.tell() > footer_offset:
		raise ValueError('index bleeds into footer')

	if check_integrity:
		pak.check_integrity(stream)

	return pak

def shall_unpack(paths,name):
	path = name.split(os.path.sep)
	for i in range(1,len(path)+1):
		prefix = os.path.join(*path[0:i])
		if prefix in paths:
			return True
	return False

def human_size(size):
	if size < 2 ** 10:
		return str(size)

	elif size < 2 ** 20:
		size = "%.1f" % (size / 2 ** 10)
		unit = "K"

	elif size < 2 ** 30:
		size = "%.1f" % (size / 2 ** 20)
		unit = "M"

	elif size < 2 ** 40:
		size = "%.1f" % (size / 2 ** 30)
		unit = "G"

	elif size < 2 ** 50:
		size = "%.1f" % (size / 2 ** 40)
		unit = "T"

	elif size < 2 ** 60:
		size = "%.1f" % (size / 2 ** 50)
		unit = "P"

	elif size < 2 ** 70:
		size = "%.1f" % (size / 2 ** 60)
		unit = "E"

	elif size < 2 ** 80:
		size = "%.1f" % (size / 2 ** 70)
		unit = "Z"

	else:
		size = "%.1f" % (size / 2 ** 80)
		unit = "Y"

	if size.endswith(".0"):
		size = size[:-2]

	return size+unit

SORT_ALIASES = {
	"s": "size",
	"S": "-size",
	"z": "zsize",
	"Z": "-zsize",
	"o": "offset",
	"O": "-offset",
	"n": "name"
}

KEY_FUNCS = {
	"size":  lambda rec: rec.uncompressed_size,
	"-size": lambda rec: -rec.uncompressed_size,

	"zsize":  lambda rec: rec.compressed_size,
	"-zsize": lambda rec: -rec.compressed_size,

	"offset":  lambda rec: rec.offset,
	"-offset": lambda rec: -rec.offset,

	"name": lambda rec: rec.filename.lower(),
}

def sort_key_func(sort):
	key_funcs = []
	for key in sort.split(","):
		key = SORT_ALIASES.get(key,key)
		try:
			func = KEY_FUNCS[key]
		except KeyError:
			raise ValueError("unknown sort key: "+key)
		key_funcs.append(func)

	return lambda rec: tuple(key_func(rec) for key_func in key_funcs)

def main(argv):
	import argparse

	# from https://gist.github.com/sampsyo/471779
	class AliasedSubParsersAction(argparse._SubParsersAction):

		class _AliasedPseudoAction(argparse.Action):
			def __init__(self, name, aliases, help):
				dest = name
				if aliases:
					dest += ' (%s)' % ','.join(aliases)
				sup = super(AliasedSubParsersAction._AliasedPseudoAction, self)
				sup.__init__(option_strings=[], dest=dest, help=help)

		def add_parser(self, name, **kwargs):
			if 'aliases' in kwargs:
				aliases = kwargs['aliases']
				del kwargs['aliases']
			else:
				aliases = []

			parser = super(AliasedSubParsersAction, self).add_parser(name, **kwargs)

			# Make the aliases work.
			for alias in aliases:
				self._name_parser_map[alias] = parser
			# Make the help text reflect them, first removing old help entry.
			if 'help' in kwargs:
				help = kwargs.pop('help')
				self._choices_actions.pop()
				pseudo_action = self._AliasedPseudoAction(name, aliases, help)
				self._choices_actions.append(pseudo_action)

			return parser

	parser = argparse.ArgumentParser(description='unpack and list Unreal Engine 4 OverHit .pak archives')
	parser.register('action', 'parsers', AliasedSubParsersAction)
	parser.set_defaults(print0=False,verbose=False,check_integrity=False,progress=False,zlib=False,command=None)

	subparsers = parser.add_subparsers(metavar='command')

	unpack_parser = subparsers.add_parser('unpack',aliases=('x',),help='unpack archive')
	unpack_parser.set_defaults(command='unpack')
	unpack_parser.add_argument('-C','--dir',type=str,default='.',
							   help='directory to write unpacked files')
	unpack_parser.add_argument('-p','--progress',action='store_true',default=False,
							   help='show progress')
	add_hack_args(unpack_parser)
	add_common_args(unpack_parser)
	unpack_parser.add_argument('files', metavar='file', nargs='*', help='files and directories to unpack')

	list_parser = subparsers.add_parser('list',aliases=('l',),help='list archive contens')
	list_parser.set_defaults(command='list')
	add_human_arg(list_parser)
	list_parser.add_argument('-d','--details',action='store_true',default=False,
							 help='print file offsets and sizes')
	list_parser.add_argument('-s','--sort',dest='sort_key_func',metavar='KEYS',type=sort_key_func,default=None,
							 help='sort file list. Comma seperated list of sort keys. Keys are "size", "zsize", "offset", and "name". '
								  'Prepend "-" to a key name to sort in descending order (descending order not supported for name).')
	add_hack_args(list_parser)
	add_common_args(list_parser)

	info_parser = subparsers.add_parser('info',aliases=('i',),help='print archive summary info')
	info_parser.set_defaults(command='info')
	add_human_arg(info_parser)
	add_integrity_arg(info_parser)
	add_archive_arg(info_parser)
	add_hack_args(info_parser)

	check_parser = subparsers.add_parser('test',aliases=('t',),help='test archive integrity')
	check_parser.set_defaults(command='test')
	add_print0_arg(check_parser)
	add_archive_arg(check_parser)
	add_hack_args(check_parser)

	args = parser.parse_args(argv)

	delim = '\0' if args.print0 else '\n'

	if args.command is None:
		parser.print_help()

	elif args.command == 'list':
		with open(args.archive,"rb") as stream:
			pak = read_index(stream, args.check_integrity, args.ignore_magic, args.encoding, args.force_version)
			pak.print_list(args.details,args.human,delim,args.sort_key_func,sys.stdout)

	elif args.command == 'info':
		with open(args.archive,"rb") as stream:
			pak = read_index(stream, args.check_integrity, args.ignore_magic, args.encoding, args.force_version)
			pak.print_info(args.human,sys.stdout)

	elif args.command == 'test':
		state = {'error_count': 0}

		def callback(ctx, message):
			state['error_count'] += 1

			if ctx is None:
				sys.stdout.write("%s%s" % (message, delim))

			elif isinstance(ctx, Record):
				sys.stdout.write("%s: %s%s" % (ctx.filename, message, delim))

			else:
				sys.stdout.write("%s: %s%s" % (ctx, message, delim))

		with open(args.archive,"rb") as stream:
			pak = read_index(stream, False, args.ignore_magic, args.encoding, args.force_version)
			pak.check_integrity(stream,callback)

		if state['error_count'] == 0:
			sys.stdout.write('All ok%s' % delim)
		else:
			sys.stdout.write('Found %d error(s)%s' % (state['error_count'], delim))
			sys.exit(1)

	elif args.command == 'unpack':
		if args.verbose:
			callback = lambda name: sys.stdout.write("%s%s" % (name, delim))
		elif args.progress:
			global nDecompOffset
			nDecompOffset = 0
			def callback(name):
				global nDecompOffset
				nDecompOffset = nDecompOffset + 1
				if nDecompOffset % 10 == 0:
					print("Decompressing %3.02f%%" % (round(nDecompOffset/len(pak)*100,2)), end="\r")
		else:
			callback = lambda name: None

		with open(args.archive,"rb") as stream:
			pak = read_index(stream, args.check_integrity, args.ignore_magic, args.encoding, args.force_version)
			if args.files:
				pak.unpack_only(stream,set(name.strip(os.path.sep) for name in args.files),args.dir,callback)
			else:
				pak.unpack(stream,args.dir,callback)

	else:
		raise ValueError('unknown command: %s' % args.command)

def add_integrity_arg(parser):
	parser.add_argument('-t','--test-integrity',action='store_true',default=False,
						help='perform extra integrity checks')

def add_archive_arg(parser):
	parser.add_argument('archive', help='Unreal Engine 4 OverHit .pak archive')

def add_print0_arg(parser):
	parser.add_argument('-0','--print0',action='store_true',default=False,
						help='seperate file names with nil bytes')

def add_verbose_arg(parser):
	parser.add_argument('-v','--verbose',action='store_true',default=False,
						help='print verbose output')

def add_human_arg(parser):
	parser.add_argument('-u','--human-readable',dest='human',action='store_true',default=False,
						help='print human readable file sizes')

def add_encoding_arg(parser):
	parser.add_argument('--encoding',type=str,default='UTF-8',
						help='charcter encoding of file names to use (default: UTF-8)')

def add_hack_args(parser):
	add_encoding_arg(parser)
	parser.add_argument('--ignore-magic',action='store_true',default=False,
						help="don't error out if file magic missmatches")
	parser.add_argument('--force-version',type=int,default=None,
						help='use this format version when parsing the file instead of the version read from the archive')

def add_common_args(parser):
	add_print0_arg(parser)
	add_verbose_arg(parser)
	add_integrity_arg(parser)
	add_archive_arg(parser)

if __name__ == '__main__':
	try:
		main(sys.argv[1:])
	except (ValueError, NotImplementedError, IOError) as exc:
		sys.stderr.write("%s\n" % exc)
		sys.exit(1)
