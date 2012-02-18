#!/usr/bin/env python
#
# Author:
#     Pawel Krawczyk (http://ipsec.pl)
# Parts based on C implementation by:
#     Ted Krovetz (tdk@acm.org)
# Port to pythonaes:
#     Guillaume Horel
#
# Licensed under GNU General Public License (GPL)
# Version 2, June 1991
# http://www.gnu.org/licenses/gpl-2.0.html

import math
try:
    from aespython.cipher_mode import CipherMode
except:
    from cipher_mode import CipherMode

class OCBMode(CipherMode):
    """
    Class implementing OCB authentication-encryption mode based on
    AES cipher in pure Python.
    """

    def __init__(self, block_cipher, block_size):
        CipherMode.__init__(self, block_cipher, block_size)

        # These routines manipulate the offsets which are used for pre- and
        # post-whitening of blockcipher invocations. The offsets represent
        # polynomials, and these routines multiply the polynomials by other
        # constant polynomials. Note that as an optimization two consecutive
        # invocations of "three_times" can be efficiently replaced:
        #    3(3(X)) == (2(2(X))) xor X
    def _times2(self, input):
        blocksize = self._block_size
        assert len(input) == blocksize
        # set carry = high bit of src
        output = [0] * blocksize
        carry = input[0] >> 7 # either 0 or 1
        for i in range(len(input)-1):
            output[i] = ((input[i] << 1) | (input[i+1] >> 7)) % 256
        output[-1] = ((input[-1] << 1) ^ (carry * 0x87)) % 256
        assert len(output) == blocksize
        return output

    def _times3(self, input):
        assert len(input) == self._block_size
        output = self._times2(input)
        output = self._xor_block(output, input)
        assert len(output) == self._block_size
        return output

    @staticmethod
    def _xor_block(input1, input2):
        assert len(input1) == len(input2)
        output = [input1[i] ^ input2[i] for i in range(len(input1))]
        return output

    def _pmac(self, header):
        """
        Calculates PMAC of optional user submitted header.

            Input: header, array of integers of arbitrary lenght
            Output: header authentication tag, array of integers

        >>> from aes import AES
        >>> aes = AES(128)
        >>> ocb = OCB(aes)
        >>> key = [0] * 16
        >>> nonce = [0] * 16
        >>> header = range(30)
        >>> ocb.setNonce(nonce)
        >>> ocb.setKey(key)
        >>> header = range(30)
        >>> ocb._pmac(header)
        [170, 167, 93, 215, 89, 168, 168, 248, 222, 127, 42, 231, 123, 50, 212, 230]
        >>> nonce = [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]
        >>> key = range(16)
        >>> ocb.setNonce(nonce)
        >>> ocb.setKey(key)
        >>> header = range(90)
        >>> ocb._pmac(header)
        [203, 23, 188, 81, 237, 161, 108, 134, 119, 64, 232, 75, 68, 126, 127, 187]
        """
        assert len(header)
        assert self._block_size

        blocksize = self._block_size

        # Break H into blocks
        m = int(max(1, math.ceil(len(header)/float(blocksize))))

        # Initialize strings used for offsets and checksums
        offset = self._block_cipher.cipher_block([0] * blocksize)
        offset = self._times3(offset)
        offset = self._times3(offset)
        checksum = [0] * blocksize

        # Accumulate the first m - 1 blocks
        # skipped if m == 1
        for i in range(m-1):
            offset = self._times2(offset)
            H_i = header[(i*blocksize):(i*blocksize)+blocksize]
            assert len(H_i) == blocksize
            xoffset = self._xor_block(H_i, offset)
            encrypted = self._block_cipher.cipher_block(xoffset)
            checksum = self._xor_block(checksum, encrypted)

        # Accumulate the final block
        offset = self._times2(offset)
        # check if full block
        H_m = header[((m-1)*blocksize):]
        assert len(H_m) <= blocksize
        if len(H_m) == blocksize:
            # complete last block
            # this is only possible if m is 1
            offset = self._times3(offset)
            checksum = self._xor_block(checksum, H_m)
        else:
            # incomplete last block
            # pad with separator binary 1
            # then pad with zeros until full block
            H_m.append(int('10000000',2))
            while len(H_m) < blocksize:
                H_m.append(0)
            assert len(H_m) == blocksize
            checksum = self._xor_block(checksum, H_m)
            offset = self._times3(offset)
            offset = self._times3(offset)

        # Compute PMAC result
        final_xor = self._xor_block(offset, checksum)
        auth = self._block_cipher.cipher_block(final_xor)
        return auth

    def encrypt_block(self, plaintext, header):
        assert self._block_size
        assert self._iv

        blocksize = self._block_size

        # Break H into blocks
        m = int(max(1, math.ceil(len(plaintext)/float(blocksize))))

        # Initialize strings used for offsets and checksums
        offset = self._block_cipher.cipher_block(self._iv)
        checksum = [0] * blocksize
        ciphertext = []

        # Encrypt and accumulate first m - 1 blocks
        # skipped if m == 1
        #for i = 1 to m - 1 do           // Skip if m < 2
        #    Offset = times2(Offset)
        #    Checksum = Checksum xor M_i
        #    C_i = Offset xor ENCIPHER(K, M_i xor Offset)
        #end for
        for i in range(m-1):
            offset = self._times2(offset)
            M_i = plaintext[(i*blocksize):(i*blocksize)+blocksize]
            assert len(M_i) == blocksize
            checksum = self._xor_block(checksum, M_i)
            xoffset = self._block_cipher.cipher_block(self._xor_block(M_i, offset))
            ciphertext += self._xor_block(offset, xoffset)
            assert len(ciphertext) % blocksize == 0

        # Encrypt and accumulate final block
        M_m = plaintext[((m-1)*blocksize):]
        # Offset = times2(Offset)
        offset = self._times2(offset)
        #  b = bitlength(M_m) // Value in 0..BLOCKLEN
        bitlength = len(M_m) * 8
        assert bitlength <= blocksize*8
        # num2str(b, BLOCKLEN)
        tmp = [0] * blocksize
        tmp[-1] = bitlength
        # Pad = ENCIPHER(K, num2str(b, BLOCKLEN) xor Offset)
        pad = self._block_cipher.cipher_block(self._xor_block(tmp, offset))
        tmp = []
        # C_m = M_m xor Pad[1..b]         // Encrypt M_m
        # this MAY be a partial size block
        C_m = self._xor_block(M_m, pad[:len(M_m)])
        ciphertext += C_m
        # Tmp = M_m || Pad[b+1..BLOCKLEN]
        tmp = M_m + pad[len(M_m):]
        assert len(tmp) == blocksize
        # Checksum = Checksum xor Tmp
        checksum = self._xor_block(tmp, checksum)

        # Compute authentication tag
        offset = self._times3(offset)
        tag = self._block_cipher.cipher_block(self._xor_block(checksum, offset))
        if len(header) > 0:
            tag = self._xor_block(tag, self._pmac(header))

        return (tag, ciphertext)


    def decrypt_block(self, header, ciphertext, tag):
        assert self._block_size


        blocksize = self._block_size

        # Break C into blocks
        m = int(max(1, math.ceil(len(ciphertext)/float(blocksize))))

        # Initialize strings used for offsets and checksums
        offset = self._block_cipher.cipher_block(self._iv)
        checksum = [0] * blocksize
        plaintext = []

#        for i = 1 to m - 1 do           // Skip if a < 2
#            Offset = times2(Offset)
#            M_i = Offset xor DECIPHER(K, C_i xor Offset)
#            Checksum = Checksum xor M_i
#        end for
        for i in range(m-1):
            offset = self._times2(offset)
            C_i = ciphertext[(i*blocksize):(i*blocksize)+blocksize]
            assert len(C_i) == blocksize
            tmp = self._block_cipher.decipher_block(self._xor_block(C_i, offset))
            M_i = self._xor_block(offset, tmp)
            checksum = self._xor_block(checksum, M_i)
            plaintext += M_i
            assert len(plaintext) % blocksize == 0

          # Decrypt and accumulate final block
#         Offset = times2(Offset)
#         b = bitlength(C_m)              // Value in 0..BLOCKLEN
#         Pad = ENCIPHER(K, num2str(b, BLOCKLEN) xor Offset)
#         M_m = C_m xor Pad[1..b]
#         Tmp = M_m || Pad[b+1..BLOCKLEN]
#         Checksum = Checksum xor Tmp
        offset = self._times2(offset)
        C_m = ciphertext[((m-1)*blocksize):]
        bitlength = len(C_m) * 8
        assert bitlength <= blocksize*8
        tmp = [0] * blocksize
        tmp[-1] = bitlength
        pad = self._block_cipher.cipher_block(self._xor_block(tmp, offset))
        tmp = []
        M_m = self._xor_block(C_m, pad[:len(C_m)])
        plaintext += M_m
        tmp = M_m + pad[len(M_m):]
        assert len(tmp) == blocksize
        checksum = self._xor_block(tmp, checksum)

        # Compute valid authentication tag
#         Offset = times3(Offset)
#         FullValidTag = ENCIPHER(K, Offset xor Checksum)
#         if bitlength(H) > 0 then
#            FullValidTag = FullValidTag xor PMAC(K, H)
#         end if
        offset = self._times3(offset)
        full_valid_tag = self._block_cipher.cipher_block(self._xor_block(offset, checksum))
        if len(header) > 0:
            full_valid_tag = self._xor_block(full_valid_tag, self._pmac(header))

        # Compute results
        if cmp(tag, full_valid_tag) == 0:
            return (True, plaintext)
        else:
            return (False, [])


if __name__ == "__main__":
    vectors = ( # header, plaintext, expected tag, expected ciphertext
        ( '', '', 'BF3108130773AD5EC70EC69E7875A7B0', '' ),
        ( '', '0001020304050607', 'A45F5FDEA5C088D1D7C8BE37CABC8C5C', 'C636B3A868F429BB' ),
        ( '', '000102030405060708090A0B0C0D0E0F', 'F7EE49AE7AA5B5E6645DB6B3966136F9', '52E48F5D19FE2D9869F0C4A4B3D2BE57' ),
        ( '', '000102030405060708090A0B0C0D0E0F1011121314151617', 'A1A50F822819D6E0A216784AC24AC84C', 'F75D6BC8B4DC8D66B836A2B08B32A636CC579E145D323BEB' ),
        ( '', '000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F', '09CA6C73F0B5C6C5FD587122D75F2AA3', 'F75D6BC8B4DC8D66B836A2B08B32A636CEC3C555037571709DA25E1BB0421A27' ),
        ( '', '000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F2021222324252627', '9DB0CDF880F73E3E10D4EB3217766688', 'F75D6BC8B4DC8D66B836A2B08B32A6369F1CD3C5228D79FD6C267F5F6AA7B231C7DFB9D59951AE9C' ),
        ( '0001020304050607', '0001020304050607', '8D059589EC3B6AC00CA31624BC3AF2C6', 'C636B3A868F429BB' ),
        ( '000102030405060708090A0B0C0D0E0F', '000102030405060708090A0B0C0D0E0F', '4DA4391BCAC39D278C7A3F1FD39041E6', '52E48F5D19FE2D9869F0C4A4B3D2BE57' ),
        ( '000102030405060708090A0B0C0D0E0F1011121314151617', '000102030405060708090A0B0C0D0E0F1011121314151617', '24B9AC3B9574D2202678E439D150F633', 'F75D6BC8B4DC8D66B836A2B08B32A636CC579E145D323BEB' ),
        ( '000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F', '000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F', '41A977C91D66F62C1E1FC30BC93823CA', 'F75D6BC8B4DC8D66B836A2B08B32A636CEC3C555037571709DA25E1BB0421A27' ),
        ( '000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F2021222324252627', '000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F2021222324252627', '65A92715A028ACD4AE6AFF4BFAA0D396', 'F75D6BC8B4DC8D66B836A2B08B32A6369F1CD3C5228D79FD6C267F5F6AA7B231C7DFB9D59951AE9C' ),
               )
    import key_expander
    import aes_cipher
    def hex2byte(hexstring):
        return map(ord, hexstring.decode("hex"))
    def byte2hex(byteslist):
        return str(bytearray(byteslist)).encode("hex")

    KE = key_expander.KeyExpander(128)
    key = hex2byte('000102030405060708090A0B0C0D0E0F')
    expanded_key = KE.expand(key)
    aes_cipher_128 = aes_cipher.AESCipher(expanded_key)
    aes_ocb_128 = OCBMode(aes_cipher_128, 16)
    iv = hex2byte('000102030405060708090A0B0C0D0E0F')
    aes_ocb_128.set_iv(iv)
    print "*** Compliance with draft-krovetz-ocb-00.txt vectors..."
    for vec in vectors:
        (header, plaintext, expected_tag, expected_ciphertext) = vec
        (tag,ciphertext) = aes_ocb_128.encrypt_block(hex2byte(plaintext), hex2byte(header))
        (dec_valid, dec_plaintext) = aes_ocb_128.decrypt_block(hex2byte(header),
                                                 hex2byte(expected_ciphertext),
                                                 hex2byte(expected_tag))
        print 'H=', header, 'M=', plaintext
        print 'T=', expected_tag, 'C=', expected_ciphertext, '(expected)'
        print 'T\'=', byte2hex(tag), 'C\'=', byte2hex(ciphertext), '(returned)'
        print "Enc T==T\':", cmp(byte2hex(tag), expected_tag.lower()) == 0, \
              "C==C\':",\
              cmp(byte2hex(ciphertext), expected_ciphertext.lower()) == 0
        print "Dec Valid=", dec_valid, \
              ", Plaintext equal=", \
              cmp(byte2hex(dec_plaintext), plaintext.lower()) == 0

    import timeit

    j = 1000
    vectors = (
        ([1]*1000, []),
        ([], [1]*1000),
        ([1]*1000, [1]*1000),
        )
    for vec in vectors:
        keylen = 128
        header, plain = vec
        setup = 'import key_expander,aes_cipher,ocb_mode; \
        KE = key_expander.KeyExpander({0}); \
        key = [0] * {1}; \
        expanded_key = KE.expand(key); \
        aes_cipher_128 = aes_cipher.AESCipher(expanded_key); \
        aes_ocb_128 = ocb_mode.OCBMode(aes_cipher_128, {1}); \
        iv = [0] * {1}; \
        from __main__ import header,plain'.format(keylen, keylen/8)
        t = timeit.Timer('aes_ocb_128.encrypt_block(header, plain)', setup)
        time = t.timeit(j)
        hlen = len(header) * j
        plen = len(plain) * j
        print hlen, "header bytes and", plen, "plaintext bytes encrypted in", time, "seconds"
        print "rate=", ((hlen+plen)*8)/1024, "kbit/sek", (hlen+plen)/1024, "kbytes/sec"

    print "*** Finished"
