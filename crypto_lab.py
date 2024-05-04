# -*- coding: utf8 -*-
__author__ = 'kisfg@hotmail.com'
"""
    设计、编写、测试一条龙开发。
        - Lib Requirement: galois AES_python pycryptodome
"""
import os, socket
from AES_Python import AES as _AES_FOR_GENERATE_KEY_
from Crypto.PublicKey import RSA
from Crypto.Cipher import PKCS1_OAEP, AES
from Crypto.Util.Padding import pad, unpad
from hashlib import sha256
from pyAesCrypt import encryptFile, decryptFile
from socket import socket, AF_INET, SOCK_STREAM, gethostname
from threading import Thread
from typing import Optional
from time import strftime, sleep

RST_COLOR: str = '\033[0m'
BREEN_COLOR: str = '\033[1;32m'
SELF_DEF_IV: bytes = b'3141592601234567'


def get_rsa_pem_key(default: int = 2048):
	keypair = RSA.generate(default)
	pub, pri = keypair.publickey(), keypair.exportKey()
	return pub, pri


def get_msg_hash(msg: str):
	hash_manager = sha256()
	hash_manager.update(msg.encode('iso-8859-1'))
	enc = hash_manager.hexdigest()
	del hash_manager
	return enc


def get_file_hash(path: str):
	hash_manager = sha256()
	with open(path, 'rb') as fd:
		while True:
			line = fd.read(1024 * 1024)
			if not line or line == b'':
				break
			hash_manager.update(line)
	res = hash_manager.hexdigest()
	del hash_manager
	return res


def get_curr_time():
	return strftime("%y-%m-%d-%H:%M:%S")


def rsa_encrypt(content: bytes, pub: bytes) -> bytes:
	if pub == b'':
		raise ValueError(f'Tried to encrypt with empty rsa-pub.')
	encryptor = PKCS1_OAEP.new(RSA.importKey(pub))
	enc = encryptor.encrypt(content)
	return enc


def rsa_decrypt(message: bytes, pri: bytes) -> bytes:
	if pri == b'':
		raise ValueError(f'Tried to decrypt with empty rsa-key.')
	decryptor = PKCS1_OAEP.new(RSA.importKey(pri))
	dec = decryptor.decrypt(message)
	return dec


def aes_encrypt_file(key: str, path2file, path2out):
	# 需要提前协商的对称密钥
	# 通信双方提前明确块大小和轮次均为 64, 不通过信道即获知。
	if key == '':
		raise ValueError(f'Tried to encrypt with empty key.')
	encryptFile(infile=path2file, outfile=path2out, passw=key)


def aes_decrypt_file(key: str, path2file, path2out):
	if key == '':
		raise ValueError(f'Tried to decrypt with empty key.')
	decryptFile(infile=path2file, outfile=path2out, passw=key)


def aes_encrypt_content(key: bytes, content: bytes):
	if key == b'':
		raise ValueError(f'Tried to encrypt stream with empty key')
	if content == b'':
		raise ValueError(f'Tried to decrypt empty content.')
	if len(content) % 128 != 0:
		padder = pad(content, 128)
	else:
		padder = content
	aes_ = AES.new(key, AES.MODE_EAX, nonce=SELF_DEF_IV)
	cipher_text = aes_.encrypt(padder)
	return cipher_text


def aes_decrypt_content(key: bytes, content: bytes):
	if key == b'':
		raise ValueError(f'Tried to encrypt stream with empty key.')
	if content == b'':
		raise ValueError(f'Tried to encrypt empty content.')
	aes_ = AES.new(key, AES.MODE_EAX, nonce=SELF_DEF_IV)
	plaintext = aes_.decrypt(content)
	plaintext = unpad(plaintext, 128)
	return plaintext


def validate_hash(gain_str: str, gain_hash: str):
	calc_hash = get_msg_hash(gain_str)
	return calc_hash == gain_hash


def validate_file(gain_file: str, gain_hash: str):
	calc_hash = get_file_hash(gain_file)
	print(f'calc-hash is: {calc_hash}, gain_hash is: {gain_hash}')
	return calc_hash == gain_hash


class stream_pass:
	"""
		简单双向加密通信。
		流程：
			- sender 明文发送自身 pub_a 与 sign_a
			- receiver 生成 session-key 并接收 sign_a
			- receiver rsa_enc(pub_a, session_key) 并返回 sign_b
			- sender 解密 session-key
			- sender 发回 aes_enc(session_key, (birth, name)) 供 receiver 校验
				- TODO: **receiver 和 sender 定义自身的白名单**
			- receiver 通过校验则等待后续通信，否则中止连接。
			- TODO: **sender 校验 receiver 完成对等操作。**
			- sender 生成 sym_aes_key 并加密原始文件
			- sender send payload <-- aes_enc(session_key, sym_aes_key)
			- receiver recv aes_dec(session_key, payload) --> sym_aes_key
			- sender 告知 (filename, filehash, filesize) 并得到 ack 后进一步发送加密文件内容
			- receiver 首先完整接收 (filename, filehash, filesize)，返回 ack，并预备接收加密文件流及其 hash
		TODO: （应用架构级）
			-  升级为去中心化 P2P 通信。
			-       断点重传或者请求续传。
			- 通过通信双方已有的信息或者使用可信第三方仲裁以克服中间人攻击的可能
	"""

	def __init__(self,
	             role: str,
	             src: str,
	             file_path: str = '',
	             out_path: str = './tmp-file',
	             sport: int = 3751,
	             rport: int = 3750):
		self.role = role  # `sender` or `receiver`
		self.pub, self.pri = get_rsa_pem_key()  # 对象固有的，用于验证身份的公私钥对
		self.use_enc_file = b''  # 加密文件用字节串
		self.use_enc_flow = ''  # iso-8859-1 等价转换

		self.name = gethostname()
		self.birth = get_curr_time()
		self.signature = get_msg_hash(self.pub.exportKey().decode('iso-8859-1') + self.birth + self.name)

		self.bname = ''
		self.bbirth = ''
		self.bsignature = ''
		self.bpub: Optional[bytes] = None  # 通信获取的发送方公钥。如非接收方，则此处为空。

		self.session_key = b''  # 会话协商密钥
		self.session_str = ''  # iso-8859-1 等价转换。

		self.out_path = out_path
		self.dec_path = ''
		self.enc_path = ''
		if os.path.exists(out_path):
			os.remove(out_path)
		self.out_fd = open(out_path, 'ab')  # 附加二进制形式写入。
		self.file_path = file_path if self.role == 'sender' else ''
		self.file_name = ''  # 接收文件名
		self.file_size = 0  # 文件尺寸
		self.file_hash = ''  # 未加密哈希

		self.__init_send__ = False  # 首次发送标记
		self.__init_recv__ = False  # 首次接收标记
		self.recv_ok = False

		self.remote_connect = None
		self.remote_addr_sport = ()  # 远端接收端口
		self.tcp_sock_send = socket(AF_INET, type=SOCK_STREAM)  # 发送出站
		self.tcp_sock_recv = socket(AF_INET, type=SOCK_STREAM)  # 入站接收
		self.tcp_sock_send.bind((src, sport))
		self.src, self.sport = src, sport
		self.rport = rport
		self.tcp_sock_recv.bind((src, rport))

	def enc_symmetric_key(self):
		if self.role == 'sender' or self.bpub is None:
			return b''
		# receiver 使用且只使用一次。
		# 需通过身份校验获取发送方公钥
		# 此后可使用此对称密钥加密所有对话。
		self.session_str = _AES_FOR_GENERATE_KEY_.key_gen()
		self.session_key = self.session_str.encode('iso-8859-1')
		return rsa_encrypt(self.session_key, self.bpub)

	def dec_symmetric_key(self, enc):
		if self.role != 'sender':
			return
		self.session_key = rsa_decrypt(enc, self.pri)
		self.session_str = self.session_key.decode('iso-8859-1')

	def file_prepare(self):
		if self.role != 'sender':
			return
		aes_encrypt_file(self.use_enc_flow, self.file_path, self.out_path)
		print('\taes_enc_ok')

	def file_decrypt(self):
		if self.role == 'sender':
			return
		aes_decrypt_file(self.use_enc_flow, self.out_path, self.file_name)
		os.remove(self.out_path)
		print('\taes_dec_ok')

	def validate_signature(self):
		_ = self.bpub.decode('iso-8859-1')
		calc_hash = get_msg_hash(_ + self.bbirth + self.bname).encode('iso-8859-1')
		return calc_hash == self.bsignature

	def try_init_sender(self, dst, rport):
		if self.__init_send__:
			return
		self.__init_send__ = True
		self.tcp_sock_send.connect((dst, rport))
		self.tcp_sock_send.settimeout(15.0)

	def just_send(self, dst, rport, data: bytes):
		self.try_init_sender(dst, rport)
		try:
			self.tcp_sock_send.sendall(data)
			sleep(0.01)
		except Exception as e:
			print(f'\t{BREEN_COLOR}[send-error]{RST_COLOR}: {e}')
			return

	def try_init_receiver(self):
		if self.__init_recv__:
			return
		self.__init_recv__ = True
		self.tcp_sock_recv.listen(1)
		self.tcp_sock_recv.settimeout(15.0)
		self.remote_connect, self.remote_addr_sport = self.tcp_sock_recv.accept()
		self.remote_connect.settimeout(15.0)

	def just_recv(self) -> bytes:
		self.try_init_receiver()
		try:
			data = self.remote_connect.recv(1024 * 1024 * 2)
			return data
		except Exception as e:
			print(f'\t{BREEN_COLOR}[recv-error]{RST_COLOR}: {e}\n')
			return b'[recv-error]: ' + f'{e}'.encode('iso-8859-1')

	# 从此处起实现安全通信协议。
	def exchange_key_challenge(self, dst, rport, state):
		if state == 0:  # key-challenge
			self.just_send(dst, rport, self.pub.exportKey())
			self.just_send(dst, rport, self.signature.encode('iso-8859-1'))
		elif state == 1:
			# 准备用发送方的公钥加密随机生成的协商公钥，并发出自身的 id，准备提供验证。
			target = self.enc_symmetric_key()
			self.just_send(dst, rport, target)
			self.just_send(dst, rport, self.signature.encode('iso-8859-1'))
		elif state == 2:
			# 已经解密了协商密钥，在此直接传加密后的信息。以供验证
			self.enc_send(dst, rport, self.birth.encode('iso-8859-1'))
			self.enc_send(dst, rport, self.name.encode('iso-8859-1'))

	# todo: 额外用于安全需求的状态

	def exchange_key_gain_response(self, state):
		if state == 0:
			self.bpub = self.just_recv()
			self.bsignature = self.just_recv()
			return False, 0

		elif state == 1:
			enc_sym_key = self.just_recv()
			print(f'gained enc sym key.')
			self.bsignature = self.just_recv()  # 接收方签名
			print(f'gained bsignature.')
			self.dec_symmetric_key(enc_sym_key)

			return False, 1

		elif state == 2 or state == 3:
			self.bbirth = self.dec_recv().decode('iso-8859-1')
			self.bname = self.dec_recv().decode('iso-8859-1')
			# TODO: 身份内容（姓名）形成的白名单判断
			if not self.validate_signature():
				self.remote_connect.close()
				self.tcp_sock_send.close()
				self.tcp_sock_recv.close()
				raise ValueError('Authencation-Failed.')

			print(f'\t{"A" if state == 2 else "B"} pass authencation.')
		else:
			return False, -404
		return True, 1

	def send_symmetry_key(self, dst, rport):

		self.use_enc_flow = _AES_FOR_GENERATE_KEY_.key_gen(16)
		self.use_enc_file = self.use_enc_flow.encode('iso-8859-1')
		print(f'symm-key: {self.use_enc_file}, {self.use_enc_flow}')
		while True:
			self.enc_send(dst, rport, self.use_enc_file)
			try:
				if self.dec_recv_bool():
					break
			except Exception as e:
				print(f'send-symm-key: {e}')
				continue

	def recv_symmetry_key(self, dst: str, rport: int):
		while True:
			try:
				self.use_enc_file = self.dec_recv()
				self.enc_send(dst, rport)
				break
			except Exception as E:
				print(f'Failed to recv file-enc-key due to {E}, will recover from exception...')
				continue
		self.use_enc_flow = self.use_enc_file.decode('iso-8859-1')
		print('recv-symm-key has recved.')

	def send_file(self, dst, rport, state):
		def read_file_by_chunk(path):
			# TODO： 改为按范围分块读取从而方便多线程编程。
			with open(path, 'rb') as fd:
				while True:
					try:
						data = fd.read(1024 * 1024)
						if not data:
							break
						yield data
					except Exception as _:
						print(f'{_}, jmp out!')
						break

		if state == 0:
			file_size = os.stat(self.out_path).st_size  # int ,
			file_hash = get_file_hash(self.file_path)
			file_name = os.path.basename(self.file_path)
			print(file_name, file_hash, file_size)
			while True:
				self.enc_send(dst, rport, str(file_size).encode('iso-8859-1'))
				self.enc_send(dst, rport, file_hash.encode('iso-8859-1'))
				self.enc_send(dst, rport, file_name.encode('iso-8859-1'))
				try:
					if self.dec_recv_bool():
						print('file0 stage end.')
						break
				except Exception as e:
					print(f'send-file-0: {e}')
					continue
			return False, 0

		for idx, _f in enumerate(read_file_by_chunk(self.out_path)):
			_fstr = _f.decode('iso-8859-1')
			curr_time = get_curr_time()
			curr_hash = get_msg_hash(_fstr + curr_time)
			print(f'begin to send in turn {idx + 1}')
			while True:
				self.just_send(dst, rport, _f)
				self.enc_send(dst, rport, curr_time.encode('iso-8859-1'))
				self.enc_send(dst, rport, curr_hash.encode('iso-8859-1'))
				try:
					if self.dec_recv_bool():
						break
				except Exception as e:
					print(e)
					continue
		while True:
			self.just_send(dst, rport, b'End of sending.')
			try:
				if self.dec_recv_bool():
					break
			except Exception as e:
				print(f'{e} appear in the last stage.')
				continue
		return True, 1

	def dec_recv_bool(self):
		data = self.just_recv()
		ret = aes_decrypt_content(self.session_key, data)
		return ret == b'OK'

	def dec_recv(self):
		data = self.just_recv()
		res = aes_decrypt_content(self.session_key, data)
		return res

	def enc_send(self, dst: str, rport: int, content: bytes = b'OK'):
		# TODO: OK 对应的序列号。
		payload = aes_encrypt_content(self.session_key, content)
		self.just_send(dst, rport, payload)
		return payload

	def recv_file(self, dst: str, rport: int, state: int):
		if state == 0:
			while True:
				try:
					self.file_size = int.from_bytes(self.dec_recv(), byteorder='little')
					self.file_hash = self.dec_recv().decode('iso-8859-1')
					self.file_name = './dec-' + self.dec_recv().decode('iso-8859-1')
					print(f'file_hash is {self.file_hash}')
					self.enc_send(dst, rport)
					return False, 0
				except Exception as e:
					print(f'Failed to recv file(size, hash, name) due to {e}.')
					continue

		while True:
			try:
				flow = self.just_recv()
				if flow == b'End of sending.':
					self.out_fd.close()
					self.enc_send(dst, rport)
					return True, 0
				cur_time = self.dec_recv().decode('iso-8859-1')
				calc_hash = self.dec_recv().decode('iso-8859-1')
				if not validate_hash(flow.decode('iso-8859-1') + cur_time, calc_hash):
					raise ValueError(f'Failed to judge the intergrity of current flow')
				print('pass validation.')
				self.out_fd.write(flow)
				self.enc_send(dst, rport)
			except Exception as e:
				print(f'Failed to recv due to {e}, will recover from exception...')
				continue


def protocol_1(entity: stream_pass, host, rport):
	print(f'Sender: the target host:rport is {host}:{rport}')
	# TODO： sleep 会有影响吗？
	sleep(1)
	entity.exchange_key_challenge(host, rport, 0)  # send pub_a
	entity.exchange_key_gain_response(1)  # get and dec session_key
	sleep(1)
	entity.exchange_key_challenge(host, rport, 2)  # send enc(session_key, id)
	sleep(1)
	entity.send_symmetry_key(host, rport)
	entity.file_prepare()
	entity.send_file(host, rport, 0)
	entity.send_file(host, rport, 1)

	entity.tcp_sock_send.close()
	entity.tcp_sock_recv.close()
	entity.remote_connect.close()


def protocol_2(entity: stream_pass, host, rport):
	print(f'Receiver: the target host:rport is {host}:{rport}')
	entity.exchange_key_gain_response(0)  # get pub_a
	sleep(1)
	entity.exchange_key_challenge(host, rport, 1)  # send enc(pub_a, session_key)
	entity.exchange_key_gain_response(2)  # validate id and confirm it or not
	entity.recv_symmetry_key(dst=host, rport=rport)
	entity.recv_file(host, rport, 0)
	entity.recv_file(host, rport, 1)

	entity.file_decrypt()
	print(validate_file(entity.file_name, entity.file_hash))
	entity.tcp_sock_send.close()
	entity.tcp_sock_recv.close()
	entity.remote_connect.close()


if __name__ == '__main__':
	print()
	"""
		本地双线程左手递右手测试 
	"""
	curr_host = '127.0.0.1'
	local = stream_pass(src=curr_host, role='sender',
	                    file_path='./[path-to-target-file]',
	                    out_path='./[path-to-enc-target-file]')
	local2 = stream_pass(src=curr_host, role='receiver', sport=3755, rport=3757)
	t1 = Thread(target=protocol_1, args=(local, curr_host, 3757))
	t2 = Thread(target=protocol_2, args=(local2, curr_host, 3750))

	t2.start()
	t1.start()
	t2.join()
	t1.join()
	del local, local2
	"""
		# protocol_1(local, '***.***.***.61', 3757)
		# 跨网段测试时需配置好两计算机的防火墙。同时只需运行接或者发的逻辑即可。
	"""
