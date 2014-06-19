/*
 * Copyright (c) 2013 Jachym Holecek <freza@circlewave.net>
 * Copyright (c) 2014 Jihyun Yu <yjh0502@gmail.com>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#define DEBUG 0
#if DEBUG == 1
#include <sys/uio.h>
#include <unistd.h>
#endif

#include <sodium.h>
#include <erl_nif.h>

/*
 * Type name normalization, utility macros.
 */

typedef unsigned int 		uint_t;
typedef unsigned long 		ulong_t;
typedef ErlNifEnv 		nif_heap_t;
typedef ERL_NIF_TERM 		nif_term_t;
typedef ErlNifFunc 		nif_func_t;
typedef ErlNifMutex 		nif_lock_t;
typedef ErlNifCond 		nif_cond_t;
typedef ErlNifResourceType 	nif_type_t;
typedef ErlNifBinary 		nif_bin_t;
typedef ErlNifTid 		nif_tid_t;
typedef ErlNifPid 		nif_pid_t;

/* Version tag on all internal data structures. */
#define SALT_VSN(maj, min, rev) 	(((maj) << 16) | ((min) << 8) | (rev))

/* Restrict processing latency by imposing payload size limit. */
#define SALT_MAX_MESSAGE_SIZE 		(16*1024)
/* XXX Measure how long crypto_[secret]box[_open] take for this size, roughly? */
/* XXX We want these calls to be equivalent to the default 1 reduction charged per NIF call */

/*
 * Globals.
 */
static const uint8_t 		salt_secretbox_zerobytes[crypto_secretbox_ZEROBYTES] = {0,}; 		/* C99 */
static const uint8_t 		salt_secretbox_boxzerobytes[crypto_secretbox_BOXZEROBYTES] = {0,}; 	/* C99 */
static const uint8_t 		salt_box_boxzerobytes[crypto_box_BOXZEROBYTES] = {0,}; 			/* C99 */
static const uint8_t 		salt_box_zerobytes[crypto_box_ZEROBYTES] = {0,}; 			/* C99 */

/* Slightly more readable this way. Variable 'hp' always calling process' heap. */
#define BADARG 			enif_make_badarg(hp)

static nif_term_t
salt_box_keypair(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	nif_bin_t 		pk;
	nif_bin_t 		sk;
	nif_term_t 		pb;
	nif_term_t 		sb;

	if (argc != 0)
		return (BADARG);

	if (! enif_alloc_binary(crypto_box_PUBLICKEYBYTES, &pk)) {
		return (BADARG);
	}
	if (! enif_alloc_binary(crypto_box_SECRETKEYBYTES, &sk)) {
		return (BADARG);
	}
	crypto_box_keypair(pk.data, sk.data);
	pb = enif_make_binary(hp, &pk);
	sb = enif_make_binary(hp, &sk);

	return enif_make_tuple2(hp, pb, sb);
}

static nif_term_t
salt_box(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_box(Plain_text, Nonce, Public_key, Secret_key) -> Cipher_text. */
	nif_bin_t 		pt;
	nif_bin_t 		nc;
	nif_bin_t 		pk;
	nif_bin_t 		sk;
	nif_bin_t 		ct;
	nif_term_t 		raw;
	nif_term_t 		sub;

	if (argc != 4)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &pt))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &nc))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &pk))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[3], &sk))
		return (BADARG);

	/* Check constraints on size and zero prefixing. */
	if (pt.size < crypto_box_ZEROBYTES || pt.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);
	if (memcmp((const void *)pt.data, &salt_box_zerobytes[0], crypto_box_ZEROBYTES) != 0)
		return (BADARG);

	if (nc.size != crypto_box_NONCEBYTES)
		return (BADARG);

	if (pk.size != crypto_box_PUBLICKEYBYTES)
		return (BADARG);

	if (sk.size != crypto_box_SECRETKEYBYTES)
		return (BADARG);

	/* Allocate space for cipher text. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(pt.size, &ct))
		return (BADARG);

	/* Perform the crypto, strip leading zeros. */
	(void)crypto_box(ct.data, pt.data, pt.size, nc.data, pk.data, sk.data);

	raw = enif_make_binary(hp, &ct);
	sub = enif_make_sub_binary(hp, raw, crypto_box_BOXZEROBYTES, ct.size - crypto_box_BOXZEROBYTES);

	return (sub);
}

static nif_term_t
salt_box_open(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_box_open(Cipher_text, Nonce, Public_key, Secret_key) -> {ok, Plain_text} | forged_or_garbled. */
	nif_bin_t 		pt;
	nif_bin_t 		nc;
	nif_bin_t 		pk;
	nif_bin_t 		sk;
	nif_bin_t 		ct;
	nif_term_t 		raw;
	nif_term_t 		sub;
	nif_term_t 		tag;

	if (argc != 4)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &ct))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &nc))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &pk))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[3], &sk))
		return (BADARG);

	/* Check constraints on size and zero prefixing. */
	if (ct.size < crypto_box_BOXZEROBYTES || ct.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);
	if (memcmp((const void *)ct.data, &salt_box_boxzerobytes[0], crypto_box_BOXZEROBYTES) != 0)
		return (BADARG);

	if (nc.size != crypto_box_NONCEBYTES)
		return (BADARG);

	if (pk.size != crypto_box_PUBLICKEYBYTES)
		return (BADARG);

	if (sk.size != crypto_box_SECRETKEYBYTES)
		return (BADARG);

	/* Allocate space for plain text. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(ct.size, &pt))
		return (BADARG);

	/* Perform the crypto, strip leading zeros and return rest if authentic. */
	if (crypto_box_open(pt.data, ct.data, ct.size, nc.data, pk.data, sk.data) != 0) {
		enif_release_binary(&pt);

		return (enif_make_atom(hp, "forged_or_garbled"));
	}

	raw = enif_make_binary(hp, &pt);
	sub = enif_make_sub_binary(hp, raw, crypto_box_ZEROBYTES, pt.size - crypto_box_ZEROBYTES);
	tag = enif_make_atom(hp, "ok");

	return (enif_make_tuple2(hp, tag, sub));
}

static nif_term_t
salt_box_beforenm(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_box_beforenm(Public_key, Secret_key) -> Context. */
	nif_bin_t 		pk;
	nif_bin_t 		sk;
	nif_bin_t 		bn;

	if (argc != 2)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_binary(hp, argv[0], &pk))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &sk))
		return (BADARG);

	/* Check size constraints. */
	if (pk.size != crypto_box_PUBLICKEYBYTES)
		return (BADARG);

	if (sk.size != crypto_box_SECRETKEYBYTES)
		return (BADARG);

	/* Allocate space for precomputed context. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(crypto_box_BEFORENMBYTES, &bn))
		return (BADARG);

	(void)crypto_box_beforenm(bn.data, pk.data, sk.data);
	return (enif_make_binary(hp, &bn));
}

static nif_term_t
salt_box_afternm(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_box_afternm(Plain_text, Nonce, Context) -> Cipher_text. */
	nif_bin_t 		pt;
	nif_bin_t 		nc;
	nif_bin_t 		bn;
	nif_bin_t 		ct;
	nif_term_t 		raw;
	nif_term_t 		sub;

	if (argc != 3)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &pt))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &nc))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &bn))
		return (BADARG);

	/* Check constraints on size and zero prefixing. */
	if (pt.size < crypto_box_ZEROBYTES || pt.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);
	if (memcmp((const void *)pt.data, &salt_box_zerobytes[0], crypto_box_ZEROBYTES) != 0)
		return (BADARG);

	if (nc.size != crypto_box_NONCEBYTES)
		return (BADARG);

	if (bn.size != crypto_box_BEFORENMBYTES)
		return (BADARG);

	/* Allocate space for precomputed context. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(pt.size, &ct))
		return (BADARG);

	/* Perform the crypto, strip leading zeros. */
	(void)crypto_box_afternm(ct.data, pt.data, pt.size, nc.data, bn.data);

	raw = enif_make_binary(hp, &ct);
	sub = enif_make_sub_binary(hp, raw, crypto_box_BOXZEROBYTES, ct.size - crypto_box_BOXZEROBYTES);

	return (sub);
}

static nif_term_t
salt_box_open_afternm(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_box_open_afternm(Cipher_text, Nonce, Context) -> {ok, Plain_text} | forged_or_garbled. */
	nif_bin_t 		ct;
	nif_bin_t 		nc;
	nif_bin_t 		bn;
	nif_bin_t 		pt;
	nif_term_t 		raw;
	nif_term_t 		sub;
	nif_term_t 		tag;

	if (argc != 3)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &ct))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &nc))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &bn))
		return (BADARG);

	/* Check constraints on size and zero prefixing. */
	if (ct.size < crypto_box_BOXZEROBYTES || ct.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);
	if (memcmp((const void *)ct.data, &salt_box_boxzerobytes[0], crypto_box_BOXZEROBYTES) != 0)
		return (BADARG);

	if (nc.size != crypto_box_NONCEBYTES)
		return (BADARG);

	if (bn.size != crypto_box_BEFORENMBYTES)
		return (BADARG);

	/* Allocate space for plain text. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(ct.size, &pt))
		return (BADARG);

	/* Perform the crypto, strip leading zeros and return rest if authentic. */
	if (crypto_box_open_afternm(pt.data, ct.data, ct.size, nc.data, bn.data) != 0) {
		enif_release_binary(&pt);

		return (enif_make_atom(hp, "forged_or_garbled"));
	}

	raw = enif_make_binary(hp, &pt);
	sub = enif_make_sub_binary(hp, raw, crypto_box_ZEROBYTES, pt.size - crypto_box_ZEROBYTES);
	tag = enif_make_atom(hp, "ok");

	return (enif_make_tuple2(hp, tag, sub));
}

static nif_term_t
salt_scalarmult(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_scalarmult(Integer, Group_p) -> Group_q. */
	nif_bin_t 		n;
	nif_bin_t 		p;
	nif_bin_t 		q;

	if (argc != 2)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_binary(hp, argv[0], &n))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &p))
		return (BADARG);

	/* Check constraints on size. */
	if (n.size != crypto_scalarmult_SCALARBYTES)
		return (BADARG);

	if (p.size != crypto_scalarmult_BYTES)
		return (BADARG);

	/* Allocate space for plain text. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(crypto_scalarmult_BYTES, &q))
		return (BADARG);
	
	crypto_scalarmult(q.data, n.data, p.data);
	return (enif_make_binary(hp, &q));
}

static nif_term_t
salt_scalarmult_base(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_scalarmult(Integer) -> Group_q. */
	nif_bin_t 		n;
	nif_bin_t 		q;

	if (argc != 1)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_binary(hp, argv[0], &n))
		return (BADARG);

	/* Check constraints on size. */
	if (n.size != crypto_scalarmult_SCALARBYTES)
		return (BADARG);

	/* Allocate space for plain text. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(crypto_scalarmult_BYTES, &q))
		return (BADARG);
	
	crypto_scalarmult_base(q.data, n.data);
	return (enif_make_binary(hp, &q));
}

static nif_term_t
salt_sign_keypair(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_sign_keypair(Pcb, From_pid, From_ref) -> enqueued | congested | exiting. */

	if (argc != 0)
		return (BADARG);

	nif_bin_t 		pk;
	nif_bin_t 		sk;
	nif_term_t 		pb;
	nif_term_t 		sb;

	if (! enif_alloc_binary(crypto_sign_PUBLICKEYBYTES, &pk)) {
		return (BADARG);
	}
	if (! enif_alloc_binary(crypto_sign_SECRETKEYBYTES, &sk)) {
		return (BADARG);
	}

	crypto_sign_keypair(pk.data, sk.data);
	pb = enif_make_binary(hp, &pk);
	sb = enif_make_binary(hp, &sk);

	return enif_make_tuple2(hp, pb, sb);
}

static nif_term_t
salt_sign(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_sign(Message, Secret_key) -> Signed_msg. */
	unsigned long long 	len;
	nif_bin_t 		pm;
	nif_bin_t 		sk;
	nif_bin_t 		sm;
	nif_term_t 		raw;

	if (argc != 2)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &pm))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &sk))
		return (BADARG);

	/* Check constraints on size. */
	if (pm.size < 1 || pm.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);

	if (sk.size != crypto_sign_SECRETKEYBYTES)
		return (BADARG);

	/* Perform the crypto, potentially adjust signed message size. */
	if (! enif_alloc_binary(pm.size + crypto_sign_BYTES, &sm))
		return (BADARG);

	(void)crypto_sign(sm.data, &len, pm.data, pm.size, sk.data);
	raw = enif_make_binary(hp, &sm);

	if (len != sm.size)
		return (enif_make_sub_binary(hp, raw, 0, len));
	else
		return (raw);
}

static nif_term_t
salt_sign_open(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_sign_open(Signed_msg, Public_key) -> {ok, Verified_msg} | forged_or_garbled. */
	unsigned long long 	len;
	nif_bin_t 		sm;
	nif_bin_t 		pk;
	nif_bin_t 		pm;
	nif_term_t 		raw;
	nif_term_t 		sub;
	nif_term_t 		tag;

	if (argc != 2)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &sm))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &pk))
		return (BADARG);

	/* Check constraints on size. */
	if (sm.size < 1 || sm.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);

	if (pk.size != crypto_sign_PUBLICKEYBYTES)
		return (BADARG);

	/* Perform the crypto, potentially adjust signed message size. */
	if (! enif_alloc_binary(sm.size + crypto_sign_BYTES, &pm))
		return (BADARG);

	if (crypto_sign_open(pm.data, &len, sm.data, sm.size, pk.data) != 0) {
		enif_release_binary(&pm);

		return (enif_make_atom(hp, "forged_or_garbled"));
	}
	raw = enif_make_binary(hp, &pm);
	tag = enif_make_atom(hp, "ok");

	if (len != sm.size)
		sub = enif_make_sub_binary(hp, raw, 0, len);
	else
		sub = raw;
	return (enif_make_tuple2(hp, tag, sub));
}

static nif_term_t
salt_secretbox(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_secretbox(Plain_text, Nonce, Secret_key) -> Cipher_text. */
	nif_bin_t 		pt;
	nif_bin_t 		nc;
	nif_bin_t 		sk;
	nif_bin_t 		ct;
	nif_term_t 		raw;
	nif_term_t 		sub;

	if (argc != 3)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &pt))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &nc))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &sk))
		return (BADARG);

	/* Check constraints on size and zero prefixing. */
	if (pt.size < crypto_secretbox_ZEROBYTES || pt.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);
	if (memcmp((const void *)pt.data, &salt_secretbox_zerobytes[0], crypto_secretbox_ZEROBYTES) != 0)
		return (BADARG);

	if (nc.size != crypto_secretbox_NONCEBYTES)
		return (BADARG);

	if (sk.size != crypto_secretbox_KEYBYTES)
		return (BADARG);

	/* Allocate space for cipher text. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(pt.size, &ct))
		return (BADARG);

	/* Perform the crypto, strip leading zeros. */
	(void)crypto_secretbox(ct.data, pt.data, pt.size, nc.data, sk.data);

	raw = enif_make_binary(hp, &ct);
	sub = enif_make_sub_binary(hp, raw, crypto_secretbox_BOXZEROBYTES, ct.size - crypto_secretbox_BOXZEROBYTES);

	return (sub);
}

static nif_term_t
salt_secretbox_open(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_secretbox_open(Cipher_text, Nonce, Secret_key) -> {ok, Plain_text} | forged_or_garbled. */
	nif_bin_t 		ct;
	nif_bin_t 		nc;
	nif_bin_t 		sk;
	nif_bin_t 		pt;
	nif_term_t 		raw;
	nif_term_t 		sub;
	nif_term_t 		tag;

	if (argc != 3)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &ct))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &nc))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &sk))
		return (BADARG);

	/* Check constraints on size and zero prefixing. */
	if (ct.size < crypto_secretbox_BOXZEROBYTES || ct.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);
	if (memcmp((const void *)ct.data, &salt_secretbox_boxzerobytes[0], crypto_secretbox_BOXZEROBYTES) != 0)
		return (BADARG);

	if (nc.size != crypto_secretbox_NONCEBYTES)
		return (BADARG);

	if (sk.size != crypto_secretbox_KEYBYTES)
		return (BADARG);

	/* Allocate space for plain text. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(ct.size, &pt))
		return (BADARG);

	/* Perform the crypto, strip leading zeros. */
	if (crypto_secretbox_open(pt.data, ct.data, ct.size, nc.data, sk.data) != 0) {
		enif_release_binary(&pt);

		return (enif_make_atom(hp, "forged_or_garbled"));
	}

	raw = enif_make_binary(hp, &pt);
	sub = enif_make_sub_binary(hp, raw, crypto_secretbox_ZEROBYTES, ct.size - crypto_secretbox_ZEROBYTES);
	tag = enif_make_atom(hp, "ok");

	return (enif_make_tuple2(hp, tag, sub));
}

static nif_term_t
salt_stream(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_stream(Byte_cnt, Nonce, Secret_key) -> Byte_stream. */
	nif_bin_t 		nc;
	nif_bin_t 		sk;
	nif_bin_t 		bs;
	uint_t 			cnt;

	if (argc != 3)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_get_uint(hp, argv[0], &cnt))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &nc))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &sk))
		return (BADARG);

	/* Check constraints on size. */
	if (cnt < 1 || cnt > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);

	if (nc.size != crypto_secretbox_NONCEBYTES)
		return (BADARG);

	if (sk.size != crypto_secretbox_KEYBYTES)
		return (BADARG);

	/* Allocate space for byte stream. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(cnt, &bs))
		return (BADARG);

	(void)crypto_stream(bs.data, bs.size, nc.data, sk.data);
	return (enif_make_binary(hp, &bs));
}

static nif_term_t
salt_stream_xor(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_stream_xor(In_text, Nonce, Secret_key) -> Out_text. */
	nif_bin_t 		it;
	nif_bin_t 		nc;
	nif_bin_t 		sk;
	nif_bin_t 		ot;

	if (argc != 3)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_binary(hp, argv[0], &it))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &nc))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &sk))
		return (BADARG);

	/* Check constraints on size. */
	if (it.size < 1 || it.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);

	if (nc.size != crypto_stream_NONCEBYTES)
		return (BADARG);

	if (sk.size != crypto_stream_KEYBYTES)
		return (BADARG);

	/* Allocate space for output byte stream. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(it.size, &ot))
		return (BADARG);

	(void)crypto_stream_xor(ot.data, it.data, it.size, nc.data, sk.data);
	return (enif_make_binary(hp, &ot));
}

static nif_term_t
salt_auth(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_auth(Message, Secret_key) -> Authenticator. */
	nif_bin_t 		ms;
	nif_bin_t 		sk;
	nif_bin_t 		au;

	if (argc != 2)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &ms))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &sk))
		return (BADARG);

	/* Check constraints on size. */
	if (ms.size < 1 || ms.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);

	if (sk.size != crypto_auth_KEYBYTES)
		return (BADARG);

	/* Allocate space for authenticator. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(crypto_auth_BYTES, &au))
		return (BADARG);

	(void)crypto_auth(au.data, ms.data, ms.size, sk.data);
	return (enif_make_binary(hp, &au));
}

static nif_term_t
salt_auth_verify(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_auth_verify(Authenticator, Message, Secret_key) -> authenticated | forged_or_garbled. */
	nif_bin_t 		au;
	nif_bin_t 		ms;
	nif_bin_t 		sk;

	if (argc != 3)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_binary(hp, argv[0], &au))
		return (BADARG);

	if (! enif_inspect_iolist_as_binary(hp, argv[1], &ms))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &sk))
		return (BADARG);

	/* Check constraints on size. */
	if (au.size != crypto_auth_BYTES)
		return (BADARG);

	if (ms.size < 1 || ms.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);

	if (sk.size != crypto_auth_KEYBYTES)
		return (BADARG);

	/* Perform the crypto. */
	if (crypto_auth_verify(au.data, ms.data, ms.size, sk.data) != 0)
		return (enif_make_atom(hp, "forged_or_garbled"));

	return (enif_make_atom(hp, "authenticated"));
}

static nif_term_t
salt_onetimeauth(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_onetimeauth(Message, Secret_key) -> Authenticator. */
	nif_bin_t 		ms;
	nif_bin_t 		sk;
	nif_bin_t 		au;

	if (argc != 2)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_iolist_as_binary(hp, argv[0], &ms))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &sk))
		return (BADARG);

	/* Check constraints on size. */
	if (ms.size < 1 || ms.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);

	if (sk.size != crypto_onetimeauth_KEYBYTES)
		return (BADARG);

	/* Allocate space for authenticator. NB: Passing ENOMEM as BADARG. */
	if (! enif_alloc_binary(crypto_onetimeauth_BYTES, &au))
		return (BADARG);

	(void)crypto_onetimeauth(au.data, ms.data, ms.size, sk.data);
	return (enif_make_binary(hp, &au));
}

static nif_term_t
salt_onetimeauth_verify(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_onetimeauth_verify(Authenticator, Message, Secret_key) -> authenticated | forged_or_garbled. */
	nif_bin_t 		au;
	nif_bin_t 		ms;
	nif_bin_t 		sk;

	if (argc != 3)
		return (BADARG);

	/* Unpack arguments ensuring they're suitably typed. */
	if (! enif_inspect_binary(hp, argv[0], &au))
		return (BADARG);

	if (! enif_inspect_iolist_as_binary(hp, argv[1], &ms))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[2], &sk))
		return (BADARG);

	/* Check constraints on size. */
	if (au.size != crypto_onetimeauth_BYTES)
		return (BADARG);

	if (ms.size < 1 || ms.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);

	if (sk.size != crypto_onetimeauth_KEYBYTES)
		return (BADARG);

	/* Perform the crypto. */
	if (crypto_onetimeauth_verify(au.data, ms.data, ms.size, sk.data) != 0)
		return (enif_make_atom(hp, "forged_or_garbled"));

	return (enif_make_atom(hp, "authenticated"));
}

static nif_term_t
salt_hash(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_hash(Message) -> Hash_bin. */
	nif_bin_t 		ms;
	nif_bin_t 		hs;

	if (argc != 1)
		return (BADARG);

	if (! enif_inspect_iolist_as_binary(hp, argv[0], &ms))
		return (BADARG);

	if (ms.size < 1 || ms.size > SALT_MAX_MESSAGE_SIZE)
		return (BADARG);

	if (! enif_alloc_binary(crypto_hash_BYTES, &hs))
		return (BADARG);

	(void)crypto_hash(hs.data, ms.data, ms.size);
	return (enif_make_binary(hp, &hs));
}

static nif_term_t
salt_verify_16(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_verify_16(Bin_x, Bin_y) -> equal | not_equal. */
	nif_bin_t 		bx;
	nif_bin_t 		by;

	if (argc != 2)
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[0], &bx))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &by))
		return (BADARG);

	if (bx.size != 16 || by.size != 16)
		return (BADARG);

	if (crypto_verify_16(bx.data, by.data) != 0)
		return (enif_make_atom(hp, "not_equal"));

	return (enif_make_atom(hp, "equal"));
}

static nif_term_t
salt_verify_32(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	/* salt_verify_32(Bin_x, Bin_y) -> equal | not_equal. */
	nif_bin_t 		bx;
	nif_bin_t 		by;

	if (argc != 2)
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[0], &bx))
		return (BADARG);

	if (! enif_inspect_binary(hp, argv[1], &by))
		return (BADARG);

	if (bx.size != 32 || by.size != 32)
		return (BADARG);

	if (crypto_verify_32(bx.data, by.data) != 0)
		return (enif_make_atom(hp, "not_equal"));

	return (enif_make_atom(hp, "equal"));
}

static nif_term_t
salt_random_bytes(nif_heap_t *hp, int argc, const nif_term_t argv[])
{
	uint_t 			cnt;
	nif_bin_t 		rb;

	if (argc != 1)
		return (BADARG);

	if (! enif_get_uint(hp, argv[0], &cnt))
		return (BADARG);

	if (! enif_alloc_binary(cnt, &rb)) {
		return (BADARG);
	}

	randombytes_buf(rb.data, rb.size);
	return enif_make_binary(hp, &rb);
}

#if DEBUG == 1
static void
print_bytes(const char *tag, nif_bin_t *buf)
{
	static const char 	*alphabet = "0123456789ABCDEF";
	uint_t 			cnt = (3 + 2*buf->size);
	uint8_t 		str[cnt];
	struct iovec  		iov[2];
	int 			i;

	/* XXX inlined UNCONST and ARRAYCOUNT... */
	iov[0].iov_base = (void *)((ulong_t)(const void *)tag);
	iov[0].iov_len = strlen(tag);
	iov[1].iov_base = str;
	iov[1].iov_len = cnt;
	
	str[0] = ' ';
	str[1] = '0';
	str[2] = 'x';

	for (i = 0; i <= buf->size; i++) {
		str[2*i + 3] = alphabet[buf->data[i] >> 4];
		str[2*i + 4] = alphabet[buf->data[i] % 16];
	}

	(void)writev(STDERR_FILENO, (const void *)&iov[0], (sizeof(iov)/sizeof(iov[0])));
}
#endif /* DEBUG */

static int
salt_load(nif_heap_t *hp, void **priv_data, nif_term_t load_info)
{
	sodium_init();
	return (0);
}

static nif_func_t salt_exports[] = {
	{"salt_box_keypair", 0, salt_box_keypair},
	{"salt_box", 4, salt_box},
	{"salt_box_open", 4, salt_box_open},
	{"salt_box_beforenm", 2, salt_box_beforenm},
	{"salt_box_afternm", 3, salt_box_afternm},
	{"salt_box_open_afternm", 3, salt_box_open_afternm},
	{"salt_scalarmult", 2, salt_scalarmult},
	{"salt_scalarmult_base", 1, salt_scalarmult_base},
	{"salt_sign_keypair", 0, salt_sign_keypair},
	{"salt_sign", 2, salt_sign},
	{"salt_sign_open", 2, salt_sign_open},
	{"salt_secretbox", 3, salt_secretbox},
	{"salt_secretbox_open", 3, salt_secretbox_open},
	{"salt_stream", 3, salt_stream},
	{"salt_stream_xor", 3, salt_stream_xor},
	{"salt_auth", 2, salt_auth},
	{"salt_auth_verify", 3, salt_auth_verify},
	{"salt_onetimeauth", 2, salt_onetimeauth},
	{"salt_onetimeauth_verify", 3, salt_onetimeauth_verify},
	{"salt_hash", 1, salt_hash},
	{"salt_verify_16", 2, salt_verify_16},
	{"salt_verify_32", 2, salt_verify_32},
	{"salt_random_bytes", 1, salt_random_bytes},
};

ERL_NIF_INIT(salt_nif, salt_exports, salt_load, NULL, NULL, NULL)
