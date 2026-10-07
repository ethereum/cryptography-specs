/* XMSS wrappers around the `eth_xmss_*` Lean exports. */
#include "wrappers.h"

/* ---- Lean externs ----------------------------------------------------- */

/* Each export consumes its object arguments, so the caller never releases them. */

extern lean_object*
eth_xmss_key_gen(
  lean_object* seed,
  uint32_t epoch_start,
  uint32_t epoch_end
);

extern lean_object*
eth_xmss_sign(
  lean_object* seed,
  uint32_t epoch_start,
  uint32_t epoch_end,
  uint32_t epoch,
  lean_object* msg
);

extern lean_object*
eth_xmss_verify(
  lean_object* pk,
  uint32_t epoch,
  lean_object* msg,
  lean_object* sig
);

extern lean_object*
eth_xmss_wots_encode(
  lean_object* pp,
  lean_object* msg,
  lean_object* rnd,
  uint32_t epoch
);

extern lean_object*
eth_xmss_tweak_hash(
  lean_object* pp,
  uint8_t tweak_type,
  uint32_t sub_position,
  uint32_t index,
  lean_object* payload
);

extern lean_object*
eth_xmss_blake2s(
  lean_object* input
);

/* ---- Local helpers (XMSS-only) --------------------------------------- */

/* Read a Python int in [0, max]; returns 0 on success. */
static int
parse_uint(
  PyObject* obj,
  unsigned long max,
  const char* name,
  unsigned long* out
) {
  if (!PyLong_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s: expected int", name);
    return 1;
  }
  unsigned long v = PyLong_AsUnsignedLong(obj);
  if (v == (unsigned long) -1 && PyErr_Occurred()) return 1;
  if (v > max) {
    PyErr_Format(PyExc_OverflowError, "%s: must be at most %lu, got %lu",
                 name, max, v);
    return 1;
  }
  *out = v;
  return 0;
}

/* Run an IO action returning a ByteArray of any length, as Python bytes. */
static PyObject*
run_io_into_pybytes(
  lean_object* io_result,
  const char* name
) {
  if (!lean_io_result_is_ok(io_result)) {
    lean_io_result_show_error(io_result);
    lean_dec(io_result);
    PyErr_Format(PyExc_RuntimeError, "%s failed", name);
    return NULL;
  }
  lean_object* ba = lean_io_result_get_value(io_result);
  PyObject* out = PyBytes_FromStringAndSize(
    (const char*) lean_sarray_cptr(ba), lean_sarray_size(ba));
  lean_dec(io_result);
  return out;
}

/* ---- Wrappers --------------------------------------------------------- */

PyObject*
py_xmss_key_gen(
  PyObject* self,
  PyObject* args
) {
  PyObject *seed_obj, *start_obj, *end_obj;
  if (!PyArg_ParseTuple(args, "OOO", &seed_obj, &start_obj, &end_obj)) return NULL;
  const uint8_t* seed = parse_bytes_of_size(seed_obj, XMSS_SEED_LEN, "seed");
  if (!seed) return NULL;
  unsigned long start, end;
  if (parse_uint(start_obj, UINT32_MAX, "epoch_start", &start)) return NULL;
  if (parse_uint(end_obj, UINT32_MAX, "epoch_end", &end)) return NULL;

  uint8_t out[XMSS_PUB_KEY_SIZE];
  lean_object* res = eth_xmss_key_gen(
    mk_bytearray(seed, XMSS_SEED_LEN), (uint32_t) start, (uint32_t) end);
  if (run_io_into_bytearray(res, out, XMSS_PUB_KEY_SIZE)) {
    PyErr_SetString(PyExc_RuntimeError, "key_gen failed");
    return NULL;
  }
  return PyBytes_FromStringAndSize((const char*) out, XMSS_PUB_KEY_SIZE);
}

PyObject*
py_xmss_sign(
  PyObject* self,
  PyObject* args
) {
  PyObject *seed_obj, *start_obj, *end_obj, *epoch_obj, *msg_obj;
  if (!PyArg_ParseTuple(args, "OOOOO",
        &seed_obj, &start_obj, &end_obj, &epoch_obj, &msg_obj)) return NULL;
  const uint8_t* seed = parse_bytes_of_size(seed_obj, XMSS_SEED_LEN, "seed");
  if (!seed) return NULL;
  unsigned long start, end, epoch;
  if (parse_uint(start_obj, UINT32_MAX, "epoch_start", &start)) return NULL;
  if (parse_uint(end_obj, UINT32_MAX, "epoch_end", &end)) return NULL;
  if (parse_uint(epoch_obj, UINT32_MAX, "epoch", &epoch)) return NULL;
  const uint8_t* msg = parse_bytes_of_size(msg_obj, XMSS_MESSAGE_LEN, "message");
  if (!msg) return NULL;

  uint8_t out[XMSS_SIG_SIZE];
  lean_object* res = eth_xmss_sign(
    mk_bytearray(seed, XMSS_SEED_LEN),
    (uint32_t) start, (uint32_t) end, (uint32_t) epoch,
    mk_bytearray(msg, XMSS_MESSAGE_LEN));
  if (run_io_into_bytearray(res, out, XMSS_SIG_SIZE)) {
    PyErr_SetString(PyExc_RuntimeError, "sign failed");
    return NULL;
  }
  return PyBytes_FromStringAndSize((const char*) out, XMSS_SIG_SIZE);
}

PyObject*
py_xmss_verify(
  PyObject* self,
  PyObject* args
) {
  PyObject *pk_obj, *epoch_obj, *msg_obj, *sig_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &pk_obj, &epoch_obj, &msg_obj, &sig_obj)) return NULL;
  const uint8_t* pk = parse_bytes_of_size(pk_obj, XMSS_PUB_KEY_SIZE, "public key");
  if (!pk) return NULL;
  unsigned long epoch;
  if (parse_uint(epoch_obj, UINT32_MAX, "epoch", &epoch)) return NULL;
  const uint8_t* msg = parse_bytes_of_size(msg_obj, XMSS_MESSAGE_LEN, "message");
  if (!msg) return NULL;
  const uint8_t* sig = parse_bytes_of_size(sig_obj, XMSS_SIG_SIZE, "signature");
  if (!sig) return NULL;

  uint8_t ok = 0;
  lean_object* res = eth_xmss_verify(
    mk_bytearray(pk, XMSS_PUB_KEY_SIZE),
    (uint32_t) epoch,
    mk_bytearray(msg, XMSS_MESSAGE_LEN),
    mk_bytearray(sig, XMSS_SIG_SIZE));
  if (run_io_into_bool(res, &ok)) {
    PyErr_SetString(PyExc_RuntimeError, "verify failed");
    return NULL;
  }
  if (ok) Py_RETURN_TRUE; else Py_RETURN_FALSE;
}

PyObject*
py_xmss_wots_encode(
  PyObject* self,
  PyObject* args
) {
  PyObject *pp_obj, *msg_obj, *rnd_obj, *epoch_obj;
  if (!PyArg_ParseTuple(args, "OOOO", &pp_obj, &msg_obj, &rnd_obj, &epoch_obj)) return NULL;
  const uint8_t* pp = parse_bytes_of_size(pp_obj, XMSS_PUBLIC_PARAM_LEN, "public parameter");
  if (!pp) return NULL;
  const uint8_t* msg = parse_bytes_of_size(msg_obj, XMSS_MESSAGE_LEN, "message");
  if (!msg) return NULL;
  const uint8_t* rnd = parse_bytes_of_size(rnd_obj, XMSS_RANDOMNESS_LEN, "randomness");
  if (!rnd) return NULL;
  unsigned long epoch;
  if (parse_uint(epoch_obj, UINT32_MAX, "epoch", &epoch)) return NULL;

  lean_object* res = eth_xmss_wots_encode(
    mk_bytearray(pp, XMSS_PUBLIC_PARAM_LEN),
    mk_bytearray(msg, XMSS_MESSAGE_LEN),
    mk_bytearray(rnd, XMSS_RANDOMNESS_LEN),
    (uint32_t) epoch);
  PyObject* digits = run_io_into_pybytes(res, "wots_encode");
  if (!digits) return NULL;
  /* An inadmissible randomizer comes back as no bytes. */
  if (PyBytes_GET_SIZE(digits) == 0) {
    Py_DECREF(digits);
    Py_RETURN_NONE;
  }
  return digits;
}

PyObject*
py_xmss_tweak_hash(
  PyObject* self,
  PyObject* args
) {
  PyObject *pp_obj, *type_obj, *sub_obj, *index_obj, *payload_obj;
  if (!PyArg_ParseTuple(args, "OOOOO",
        &pp_obj, &type_obj, &sub_obj, &index_obj, &payload_obj)) return NULL;
  const uint8_t* pp = parse_bytes_of_size(pp_obj, XMSS_PUBLIC_PARAM_LEN, "public parameter");
  if (!pp) return NULL;
  unsigned long tweak_type, sub_position, index;
  if (parse_uint(type_obj, UINT8_MAX, "tweak_type", &tweak_type)) return NULL;
  if (parse_uint(sub_obj, UINT32_MAX, "sub_position", &sub_position)) return NULL;
  if (parse_uint(index_obj, UINT32_MAX, "index", &index)) return NULL;
  if (!PyBytes_Check(payload_obj)) {
    PyErr_SetString(PyExc_TypeError, "payload must be bytes");
    return NULL;
  }

  uint8_t out[XMSS_DIGEST_LEN];
  lean_object* res = eth_xmss_tweak_hash(
    mk_bytearray(pp, XMSS_PUBLIC_PARAM_LEN),
    (uint8_t) tweak_type, (uint32_t) sub_position, (uint32_t) index,
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(payload_obj),
                 PyBytes_GET_SIZE(payload_obj)));
  if (run_io_into_bytearray(res, out, XMSS_DIGEST_LEN)) {
    PyErr_SetString(PyExc_RuntimeError, "tweak_hash failed");
    return NULL;
  }
  return PyBytes_FromStringAndSize((const char*) out, XMSS_DIGEST_LEN);
}

PyObject*
py_xmss_blake2s(
  PyObject* self,
  PyObject* args
) {
  PyObject* input_obj;
  if (!PyArg_ParseTuple(args, "O", &input_obj)) return NULL;
  if (!PyBytes_Check(input_obj)) {
    PyErr_SetString(PyExc_TypeError, "input must be bytes");
    return NULL;
  }

  lean_object* res = eth_xmss_blake2s(
    mk_bytearray((const uint8_t*) PyBytes_AS_STRING(input_obj),
                 PyBytes_GET_SIZE(input_obj)));
  return run_io_into_pybytes(res, "blake2s");
}
