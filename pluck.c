/*-
 Copyright 2009 Colin Percival, 2011 ArtForz, 2011-2014 pooler, 2015 Jordan Earls, 2015 ocminer (admin at suprnova.cc)
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file was originally written by Colin Percival as part of the Tarsnap
 * online backup system.
 */

#include <stdlib.h>
#include <string.h>

#include <inttypes.h>

#include <stdbool.h>
#include <inttypes.h>
#include <sys/time.h>
#include <pthread.h>


#define ROTL(a, b) (((a) << (b)) | ((a) >> (32 - (b))))


#define bswap_32(x) ((((x) << 24) & 0xff000000u) | (((x) << 8) & 0x00ff0000u) \
                   | (((x) >> 8) & 0x0000ff00u) | (((x) >> 24) & 0x000000ffu))

static inline uint32_t swab32(uint32_t v)
{
#ifdef WANT_BUILTIN_BSWAP
        return __builtin_bswap32(v);
#else
        return bswap_32(v);
#endif
}



static __inline uint32_t
be32dec(const void *pp)
{
	const uint8_t *p = (uint8_t const *)pp;

	return ((uint32_t)(p[3]) + ((uint32_t)(p[2]) << 8) +
	    ((uint32_t)(p[1]) << 16) + ((uint32_t)(p[0]) << 24));
}

static __inline void
be32enc(void *pp, uint32_t x)
{
	uint8_t * p = (uint8_t *)pp;

	p[3] = x & 0xff;
	p[2] = (x >> 8) & 0xff;
	p[1] = (x >> 16) & 0xff;
	p[0] = (x >> 24) & 0xff;
}

static __inline uint32_t
le32dec(const void *pp)
{
	const uint8_t *p = (uint8_t const *)pp;

	return ((uint32_t)(p[0]) + ((uint32_t)(p[1]) << 8) +
	    ((uint32_t)(p[2]) << 16) + ((uint32_t)(p[3]) << 24));
}

static __inline void
le32enc(void *pp, uint32_t x)
{
	uint8_t * p = (uint8_t *)pp;

	p[0] = x & 0xff;
	p[1] = (x >> 8) & 0xff;
	p[2] = (x >> 16) & 0xff;
	p[3] = (x >> 24) & 0xff;
}


typedef struct SHA256Context {
	uint32_t state[8];
	uint32_t count[2];
	unsigned char buf[64];
} SHA256_CTX;

typedef struct HMAC_SHA256Context {
	SHA256_CTX ictx;
	SHA256_CTX octx;
} HMAC_SHA256_CTX;



static const uint32_t sha256_k[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

static const uint32_t sha256_h[8] = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};


void sha256_init(uint32_t *state)
{
        memcpy(state, sha256_h, 32);
}


/* Elementary functions used by SHA256 */
#define Ch(x, y, z)     ((x & (y ^ z)) ^ z)
#define Maj(x, y, z)    ((x & (y | z)) | (y & z))
#define ROTR(x, n)      ((x >> n) | (x << (32 - n)))
#define S0(x)           (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define S1(x)           (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define s0(x)           (ROTR(x, 7) ^ ROTR(x, 18) ^ (x >> 3))
#define s1(x)           (ROTR(x, 17) ^ ROTR(x, 19) ^ (x >> 10))

/* SHA256 round function */
#define RND(a, b, c, d, e, f, g, h, k) \
        do { \
                t0 = h + S1(e) + Ch(e, f, g) + k; \
                t1 = S0(a) + Maj(a, b, c); \
                d += t0; \
                h  = t0 + t1; \
        } while (0)

/* Adjusted round function for rotating state */
#define RNDr(S, W, i) \
        RND(S[(64 - i) % 8], S[(65 - i) % 8], \
            S[(66 - i) % 8], S[(67 - i) % 8], \
            S[(68 - i) % 8], S[(69 - i) % 8], \
            S[(70 - i) % 8], S[(71 - i) % 8], \
            W[i] + sha256_k[i])




void sha256_transform(uint32_t *state, const uint32_t *block, int swap)
{
        uint32_t W[64];
        uint32_t S[8];
        uint32_t t0, t1;
        int i;

        /* 1. Prepare message schedule W. */
        if (swap) {
                for (i = 0; i < 16; i++)
                        W[i] = swab32(block[i]);
        } else
                memcpy(W, block, 64);
        for (i = 16; i < 64; i += 2) {
                W[i]   = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];
                W[i+1] = s1(W[i - 1]) + W[i - 6] + s0(W[i - 14]) + W[i - 15];
        }

        /* 2. Initialize working variables. */
        memcpy(S, state, 32);

        /* 3. Mix. */
        RNDr(S, W,  0);
        RNDr(S, W,  1);
        RNDr(S, W,  2);
        RNDr(S, W,  3);
        RNDr(S, W,  4);
        RNDr(S, W,  5);
        RNDr(S, W,  6);
        RNDr(S, W,  7);
        RNDr(S, W,  8);
        RNDr(S, W,  9);
        RNDr(S, W, 10);
        RNDr(S, W, 11);
        RNDr(S, W, 12);
        RNDr(S, W, 13);
        RNDr(S, W, 14);
        RNDr(S, W, 15);
        RNDr(S, W, 16);
        RNDr(S, W, 17);
        RNDr(S, W, 18);
        RNDr(S, W, 19);
        RNDr(S, W, 20);
        RNDr(S, W, 21);
        RNDr(S, W, 22);
        RNDr(S, W, 23);
        RNDr(S, W, 24);
        RNDr(S, W, 25);
        RNDr(S, W, 26);
        RNDr(S, W, 27);
        RNDr(S, W, 28);
        RNDr(S, W, 29);
        RNDr(S, W, 30);
        RNDr(S, W, 31);
        RNDr(S, W, 32);
        RNDr(S, W, 33);
        RNDr(S, W, 34);
        RNDr(S, W, 35);
        RNDr(S, W, 36);
        RNDr(S, W, 37);
        RNDr(S, W, 38);
        RNDr(S, W, 39);
        RNDr(S, W, 40);
        RNDr(S, W, 41);
        RNDr(S, W, 42);
        RNDr(S, W, 43);
        RNDr(S, W, 44);
        RNDr(S, W, 45);
        RNDr(S, W, 46);
        RNDr(S, W, 47);
        RNDr(S, W, 48);
        RNDr(S, W, 49);
        RNDr(S, W, 50);
        RNDr(S, W, 51);
        RNDr(S, W, 52);
        RNDr(S, W, 53);
        RNDr(S, W, 54);
        RNDr(S, W, 55);
        RNDr(S, W, 56);
        RNDr(S, W, 57);
        RNDr(S, W, 58);
        RNDr(S, W, 59);
        RNDr(S, W, 60);
        RNDr(S, W, 61);
        RNDr(S, W, 62);
        RNDr(S, W, 63);

        /* 4. Mix local working variables into global state */
        for (i = 0; i < 8; i++)
                state[i] += S[i];
}


static void blkcpy(void *, void *, size_t);
static void blkxor(void *, void *, size_t);
static void salsa20_8(uint32_t[16]);
static void blockmix_salsa8(uint32_t *, uint32_t *, uint32_t *, size_t);

static void
blkcpy(void * dest, void * src, size_t len)
{
	size_t * D = dest;
	size_t * S = src;
	size_t L = len / sizeof(size_t);
	size_t i;

	for (i = 0; i < L; i++)
		D[i] = S[i];
}

static void
blkxor(void * dest, void * src, size_t len)
{
	size_t * D = dest;
	size_t * S = src;
	size_t L = len / sizeof(size_t);
	size_t i;

	for (i = 0; i < L; i++)
		D[i] ^= S[i];
}

/**
 * salsa20_8(B):
 * Apply the salsa20/8 core to the provided block.
 */
static void
salsa20_8(uint32_t B[16])
{
	uint32_t x[16];
	size_t i;

	blkcpy(x, B, 64);
	for (i = 0; i < 8; i += 2) {
#define R(a,b) (((a) << (b)) | ((a) >> (32 - (b))))
		/* Operate on columns. */
		x[ 4] ^= R(x[ 0]+x[12], 7);  x[ 8] ^= R(x[ 4]+x[ 0], 9);
		x[12] ^= R(x[ 8]+x[ 4],13);  x[ 0] ^= R(x[12]+x[ 8],18);

		x[ 9] ^= R(x[ 5]+x[ 1], 7);  x[13] ^= R(x[ 9]+x[ 5], 9);
		x[ 1] ^= R(x[13]+x[ 9],13);  x[ 5] ^= R(x[ 1]+x[13],18);

		x[14] ^= R(x[10]+x[ 6], 7);  x[ 2] ^= R(x[14]+x[10], 9);
		x[ 6] ^= R(x[ 2]+x[14],13);  x[10] ^= R(x[ 6]+x[ 2],18);

		x[ 3] ^= R(x[15]+x[11], 7);  x[ 7] ^= R(x[ 3]+x[15], 9);
		x[11] ^= R(x[ 7]+x[ 3],13);  x[15] ^= R(x[11]+x[ 7],18);

		/* Operate on rows. */
		x[ 1] ^= R(x[ 0]+x[ 3], 7);  x[ 2] ^= R(x[ 1]+x[ 0], 9);
		x[ 3] ^= R(x[ 2]+x[ 1],13);  x[ 0] ^= R(x[ 3]+x[ 2],18);

		x[ 6] ^= R(x[ 5]+x[ 4], 7);  x[ 7] ^= R(x[ 6]+x[ 5], 9);
		x[ 4] ^= R(x[ 7]+x[ 6],13);  x[ 5] ^= R(x[ 4]+x[ 7],18);

		x[11] ^= R(x[10]+x[ 9], 7);  x[ 8] ^= R(x[11]+x[10], 9);
		x[ 9] ^= R(x[ 8]+x[11],13);  x[10] ^= R(x[ 9]+x[ 8],18);

		x[12] ^= R(x[15]+x[14], 7);  x[13] ^= R(x[12]+x[15], 9);
		x[14] ^= R(x[13]+x[12],13);  x[15] ^= R(x[14]+x[13],18);
#undef R
	}
	for (i = 0; i < 16; i++)
		B[i] += x[i];
}

/**
 * blockmix_salsa8(Bin, Bout, X, r):
 * Compute Bout = BlockMix_{salsa20/8, r}(Bin).  The input Bin must be 128r
 * bytes in length; the output Bout must also be the same size.  The
 * temporary space X must be 64 bytes.
 */
static void
blockmix_salsa8(uint32_t * Bin, uint32_t * Bout, uint32_t * X, size_t r)
{
	size_t i;

	/* 1: X <-- B_{2r - 1} */
	blkcpy(X, &Bin[(2 * r - 1) * 16], 64);

	/* 2: for i = 0 to 2r - 1 do */
	for (i = 0; i < 2 * r; i += 2) {
		/* 3: X <-- H(X \xor B_i) */
		blkxor(X, &Bin[i * 16], 64);
		salsa20_8(X);

		/* 4: Y_i <-- X */
		/* 6: B' <-- (Y_0, Y_2 ... Y_{2r-2}, Y_1, Y_3 ... Y_{2r-1}) */
		blkcpy(&Bout[i * 8], X, 64);

		/* 3: X <-- H(X \xor B_i) */
		blkxor(X, &Bin[i * 16 + 16], 64);
		salsa20_8(X);

		/* 4: Y_i <-- X */
		/* 6: B' <-- (Y_0, Y_2 ... Y_{2r-2}, Y_1, Y_3 ... Y_{2r-1}) */
		blkcpy(&Bout[i * 8 + r * 16], X, 64);
	}
}


/* FUn starts here ...*/


//note, this is 64 bytes
static inline void xor_salsa8(uint32_t B[16], const uint32_t Bx[16])
{
    uint32_t x00,x01,x02,x03,x04,x05,x06,x07,x08,x09,x10,x11,x12,x13,x14,x15;
    int i;
 
    x00 = (B[ 0] ^= Bx[ 0]);
    x01 = (B[ 1] ^= Bx[ 1]);
    x02 = (B[ 2] ^= Bx[ 2]);
    x03 = (B[ 3] ^= Bx[ 3]);
    x04 = (B[ 4] ^= Bx[ 4]);
    x05 = (B[ 5] ^= Bx[ 5]);
    x06 = (B[ 6] ^= Bx[ 6]);
    x07 = (B[ 7] ^= Bx[ 7]);
    x08 = (B[ 8] ^= Bx[ 8]);
    x09 = (B[ 9] ^= Bx[ 9]);
    x10 = (B[10] ^= Bx[10]);
    x11 = (B[11] ^= Bx[11]);
    x12 = (B[12] ^= Bx[12]);
    x13 = (B[13] ^= Bx[13]);
    x14 = (B[14] ^= Bx[14]);
    x15 = (B[15] ^= Bx[15]);
    for (i = 0; i < 8; i += 2) {
        /* Operate on columns. */
        x04 ^= ROTL(x00 + x12,  7);  x09 ^= ROTL(x05 + x01,  7);
        x14 ^= ROTL(x10 + x06,  7);  x03 ^= ROTL(x15 + x11,  7);
 
        x08 ^= ROTL(x04 + x00,  9);  x13 ^= ROTL(x09 + x05,  9);
        x02 ^= ROTL(x14 + x10,  9);  x07 ^= ROTL(x03 + x15,  9);
 
        x12 ^= ROTL(x08 + x04, 13);  x01 ^= ROTL(x13 + x09, 13);
        x06 ^= ROTL(x02 + x14, 13);  x11 ^= ROTL(x07 + x03, 13);
 
        x00 ^= ROTL(x12 + x08, 18);  x05 ^= ROTL(x01 + x13, 18);
        x10 ^= ROTL(x06 + x02, 18);  x15 ^= ROTL(x11 + x07, 18);
 
        /* Operate on rows. */
        x01 ^= ROTL(x00 + x03,  7);  x06 ^= ROTL(x05 + x04,  7);
        x11 ^= ROTL(x10 + x09,  7);  x12 ^= ROTL(x15 + x14,  7);
 
        x02 ^= ROTL(x01 + x00,  9);  x07 ^= ROTL(x06 + x05,  9);
        x08 ^= ROTL(x11 + x10,  9);  x13 ^= ROTL(x12 + x15,  9);
 
        x03 ^= ROTL(x02 + x01, 13);  x04 ^= ROTL(x07 + x06, 13);
        x09 ^= ROTL(x08 + x11, 13);  x14 ^= ROTL(x13 + x12, 13);
 
        x00 ^= ROTL(x03 + x02, 18);  x05 ^= ROTL(x04 + x07, 18);
        x10 ^= ROTL(x09 + x08, 18);  x15 ^= ROTL(x14 + x13, 18);
    }
    B[ 0] += x00;
    B[ 1] += x01;
    B[ 2] += x02;
    B[ 3] += x03;
    B[ 4] += x04;
    B[ 5] += x05;
    B[ 6] += x06;
    B[ 7] += x07;
    B[ 8] += x08;
    B[ 9] += x09;
    B[10] += x10;
    B[11] += x11;
    B[12] += x12;
    B[13] += x13;
    B[14] += x14;
    B[15] += x15;
}
 
#ifdef USE_SSE2
 
static inline void xor_salsa8_sse2(__m128i B[4], const __m128i Bx[4])
{
  __m128i X0, X1, X2, X3;
  __m128i T;
  int i;
 
  X0 = B[0] = _mm_xor_si128(B[0], Bx[0]);
  X1 = B[1] = _mm_xor_si128(B[1], Bx[1]);
  X2 = B[2] = _mm_xor_si128(B[2], Bx[2]);
  X3 = B[3] = _mm_xor_si128(B[3], Bx[3]);
 
  for (i = 0; i < 8; i += 2) {
    /* Operate on "columns". */
    T = _mm_add_epi32(X0, X3);
    X1 = _mm_xor_si128(X1, _mm_slli_epi32(T, 7));
    X1 = _mm_xor_si128(X1, _mm_srli_epi32(T, 25));
    T = _mm_add_epi32(X1, X0);
    X2 = _mm_xor_si128(X2, _mm_slli_epi32(T, 9));
    X2 = _mm_xor_si128(X2, _mm_srli_epi32(T, 23));
    T = _mm_add_epi32(X2, X1);
    X3 = _mm_xor_si128(X3, _mm_slli_epi32(T, 13));
    X3 = _mm_xor_si128(X3, _mm_srli_epi32(T, 19));
    T = _mm_add_epi32(X3, X2);
    X0 = _mm_xor_si128(X0, _mm_slli_epi32(T, 18));
    X0 = _mm_xor_si128(X0, _mm_srli_epi32(T, 14));
 
    /* Rearrange data. */
    X1 = _mm_shuffle_epi32(X1, 0x93);
    X2 = _mm_shuffle_epi32(X2, 0x4E);
    X3 = _mm_shuffle_epi32(X3, 0x39);
 
    /* Operate on "rows". */
    T = _mm_add_epi32(X0, X1);
    X3 = _mm_xor_si128(X3, _mm_slli_epi32(T, 7));
    X3 = _mm_xor_si128(X3, _mm_srli_epi32(T, 25));
    T = _mm_add_epi32(X3, X0);
    X2 = _mm_xor_si128(X2, _mm_slli_epi32(T, 9));
    X2 = _mm_xor_si128(X2, _mm_srli_epi32(T, 23));
    T = _mm_add_epi32(X2, X3);
    X1 = _mm_xor_si128(X1, _mm_slli_epi32(T, 13));
    X1 = _mm_xor_si128(X1, _mm_srli_epi32(T, 19));
    T = _mm_add_epi32(X1, X2);
    X0 = _mm_xor_si128(X0, _mm_slli_epi32(T, 18));
    X0 = _mm_xor_si128(X0, _mm_srli_epi32(T, 14));
 
    /* Rearrange data. */
    X1 = _mm_shuffle_epi32(X1, 0x39);
    X2 = _mm_shuffle_epi32(X2, 0x4E);
    X3 = _mm_shuffle_epi32(X3, 0x93);
  }
 
  B[0] = _mm_add_epi32(B[0], X0);
  B[1] = _mm_add_epi32(B[1], X1);
  B[2] = _mm_add_epi32(B[2], X2);
  B[3] = _mm_add_epi32(B[3], X3);
}
 
#endif
 
 
 
static inline void assert(int cond)
{
  if(!cond)
  {
    //printf("error\n");
    exit(1);
  }
}
//computes a single sha256 hash
void sha256_hash(unsigned char *hash, const unsigned char *data, int len)
{
  uint32_t S[16] __attribute__((aligned(32))), T[16] __attribute__((aligned(32)));
  int i, r;
 
  sha256_init(S);
  for (r = len; r > -9; r -= 64) {
    if (r < 64)
      memset(T, 0, 64);
    memcpy(T, data + len - r, r > 64 ? 64 : (r < 0 ? 0 : r));
    if (r >= 0 && r < 64)
      ((unsigned char *)T)[r] = 0x80;
    for (i = 0; i < 16; i++)
      T[i] = be32dec(T + i);
    if (r < 56)
      T[15] = 8 * len;
    sha256_transform(S, T, 0);
  }
  for (i = 0; i < 8; i++)
    be32enc((uint32_t *)hash + i, S[i]);
}
 
//hash exactly 64 bytes (ie, sha256 block size)
void sha256_hash512(unsigned char *hash, const unsigned char *data)
{
  uint32_t S[16] __attribute__((aligned(32))), T[16] __attribute__((aligned(32)));
  int i;
 
  sha256_init(S);
 
    memcpy(T, data, 64);
    for (i = 0; i < 16; i++)
      T[i] = be32dec(T + i);
    sha256_transform(S, T, 0);
 
    memset(T, 0, 64);
    //memcpy(T, data + 64, 0);
    ((unsigned char *)T)[0] = 0x80;
    for (i = 0; i < 16; i++)
      T[i] = be32dec(T + i);
      T[15] = 8 * 64;
    sha256_transform(S, T, 0);
 
  for (i = 0; i < 8; i++)
    be32enc((uint32_t *)hash + i, S[i]);
}
 
void pluck_hash(uint32_t *hash, const uint32_t *data) 
{
    const int N = 128;
         uint8_t *hashbuffer = malloc(N * 1024);
    int size= N * 1024;
    memset(hashbuffer, 0, 64);
    sha256_hash(&hashbuffer[0], data, 80);
   
    int i; 
    for (i = 64; i < size-32; i+=32)
    {
        //i-4 because we use integers for all references against this, and we don't want to go 3 bytes over the defined area
        int randmax = i-4; //we could use size here, but then it's probable to use 0 as the value in most cases
        uint32_t joint[16];
        uint32_t randbuffer[16];
//        assert(i-32>0);
//        assert(i<size);
        uint32_t randseed[16];
        assert(sizeof(int)*16 == 64);
 
        //setup randbuffer to be an array of random indexes
        memcpy(randseed, &hashbuffer[i-64], 64);
        if(i>128)
        {
            memcpy(randbuffer, &hashbuffer[i-128], 64);
        }else
        {
            memset(&randbuffer, 0, 64);
        }
        xor_salsa8(randbuffer, randseed);
        memcpy(joint, &hashbuffer[i-32], 32);
        //use the last hash value as the seed
	int j;
        for (j = 32; j < 64; j+=4)
        {
            assert((j - 32) / 2 < 16);
            //every other time, change to next random index
            uint32_t rand = randbuffer[(j - 32)/4] % (randmax-32); //randmax - 32 as otherwise we go beyond memory that's already been written to
//            assert(j>0 && j<64);
//            assert(rand<size);
//            assert(j/2 < 64);
            joint[j/4] = *((uint32_t*)&hashbuffer[rand]);
        }
//        assert(i>=0 && i+32<size);
 
        sha256_hash512(&hashbuffer[i], joint);
 
        //setup randbuffer to be an array of random indexes
        memcpy(randseed, &hashbuffer[i-32], 64); //use last hash value and previous hash value(post-mixing)
        if(i>128)
        {
            memcpy(randbuffer, &hashbuffer[i-128], 64);
        }else
        {
            memset(randbuffer, 0, 64);
        }
        //#ifdef USE_SSE2
        //xor_salsa8_sse2((__m128i*)randbuffer, (__m128i*)randseed);
        //#else
        xor_salsa8(randbuffer, randseed);
       // #endif
	int k; 
        //use the last hash value as the seed
        for (k = 0; k < 32; k+=2)
        {
//            assert(j/4 < 16);
            uint32_t rand = randbuffer[k/2] % randmax;
//            assert(rand < size);
//            assert((j/4)+i >= 0 && (j/4)+i < size);
//            assert(j + i -4 < i + 32); //assure we dont' access beyond the hash
            *((uint32_t*)&hashbuffer[rand]) = *((uint32_t*)&hashbuffer[k + i - 4]);
        }
    }
    //note: off-by-one error is likely here...    
    int l;
    for (l = size-64-1; l >= 64; l -= 64)      
    {      
//      assert(i-64 >= 0);      
//      assert(i+64<size);    
      sha256_hash512(&hashbuffer[l-64], &hashbuffer[l]);
     }
 
 
    memcpy((unsigned char*)hash, hashbuffer, 32);
   
    free(hashbuffer);
}

