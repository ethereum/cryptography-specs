/*
 * CPython extension entry point. Boots the Lean runtime, wires up the
 * spec-preset size constants, and assembles the method table from the
 * per-domain wrappers.
 */
#include "wrappers.h"

/* ---- Spec sizes (populated in `PyInit__native`) ---------------------- */

size_t BYTES_PER_PUBKEY;
size_t BYTES_PER_SIGNATURE;

size_t BYTES_PER_FIELD_ELEMENT;
size_t BYTES_PER_COMMITMENT;
size_t BYTES_PER_PROOF;
size_t FIELD_ELEMENTS_PER_BLOB;
size_t BYTES_PER_BLOB;
size_t FIELD_ELEMENTS_PER_CELL;
size_t BYTES_PER_CELL;
size_t CELLS_PER_EXT_BLOB;

size_t XMSS_DIGEST_LEN;
size_t XMSS_PUBLIC_PARAM_LEN;
size_t XMSS_MESSAGE_LEN;
size_t XMSS_RANDOMNESS_LEN;
size_t XMSS_SEED_LEN;
size_t XMSS_CODE_LENGTH;
size_t XMSS_LOG_LIFETIME;
size_t XMSS_PUB_KEY_SIZE;
size_t XMSS_SIG_SIZE;

/* ---- Lean externs: size accessors ------------------------------------ */

extern uint64_t
eth_bls_const_bytes_per_pubkey(
  uint8_t unit
);

extern uint64_t
eth_bls_const_bytes_per_signature(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_field_element(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_commitment(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_proof(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_field_elements_per_blob(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_blob(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_field_elements_per_cell(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_bytes_per_cell(
  uint8_t unit
);

extern uint64_t
eth_kzg_const_cells_per_ext_blob(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_digest_len(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_public_param_len(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_message_len(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_randomness_len(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_seed_len(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_code_length(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_log_lifetime(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_pub_key_size(
  uint8_t unit
);

extern uint64_t
eth_xmss_const_sig_size(
  uint8_t unit
);

/* ---- Lean externs: runtime + module init ----------------------------- */

extern void
lean_initialize_runtime_module(void);

/* We boot the sub-umbrellas directly rather than the top-level
 * `EthCryptographySpecs` module: Lake produces a `.c` file for the
 * library root but does *not* compile it to a `.c.o.export`, so its
 * init symbol would never get linked in. Each sub-umbrella's init
 * idempotently calls `initialize_Init` for the Lean stdlib, so this
 * covers everything the dropped umbrella init did. */
extern lean_object*
initialize_EthCryptographySpecs_EthCryptographySpecs_Bls(
  uint8_t builtin
);

extern lean_object*
initialize_EthCryptographySpecs_EthCryptographySpecs_Kzg(
  uint8_t builtin
);

extern lean_object*
initialize_EthCryptographySpecs_EthCryptographySpecs_Xmss(
  uint8_t builtin
);

/*
 * Note on linker hygiene:
 *   `lean_initialize()` and `initialize_Lean` live in libleancpp.a's
 *   `init.cpp.o`, which references most of the Lean *compiler* and
 *   would drag in the 224MB `libLean.a`. We avoid them by calling only
 *   `lean_initialize_runtime_module()` (from libleanrt.a, which is the
 *   minimal runtime: GC, allocator, IO primitives) plus our package's
 *   per-module init `initialize_EthCryptographySpecs_*`. Together that's
 *   enough to run any code we'd actually call from Python.
 */

/* ---- Lean ↔ C marshalling helpers ------------------------------------ */

lean_object*
mk_bytearray(
  const uint8_t* data,
  size_t len
) {
  lean_object* arr = lean_alloc_sarray(1, len, len);
  memcpy(lean_sarray_cptr(arr), data, len);
  return arr;
}

lean_object*
mk_bytearray_array(
  const uint8_t* data,
  size_t n,
  size_t stride
) {
  lean_object* arr = lean_alloc_array(n, n);
  for (size_t i = 0; i < n; i++) {
    lean_array_set_core(arr, i, mk_bytearray(data + i * stride, stride));
  }
  return arr;
}

/* Run an IO action and copy its inner ByteArray into `out`/`out_len`.
 * `lean_io_result_get_value` returns a *borrowed* reference; do NOT
 * `lean_dec` the inner value separately. Returns 0 on success. */
int
run_io_into_bytearray(
  lean_object* io_result,
  uint8_t* out,
  size_t out_len
) {
  if (!lean_io_result_is_ok(io_result)) {
    lean_io_result_show_error(io_result);
    lean_dec(io_result);
    return 1;
  }
  lean_object* ba = lean_io_result_get_value(io_result);
  size_t got = lean_sarray_size(ba);
  if (got != out_len) {
    lean_dec(io_result);
    return 1;
  }
  memcpy(out, lean_sarray_cptr(ba), out_len);
  lean_dec(io_result);
  return 0;
}

/* Run an IO action returning a UInt8 boolean. */
int
run_io_into_bool(
  lean_object* io_result,
  uint8_t* out_ok
) {
  if (!lean_io_result_is_ok(io_result)) {
    lean_io_result_show_error(io_result);
    lean_dec(io_result);
    return 1;
  }
  *out_ok = lean_unbox(lean_io_result_get_value(io_result));
  lean_dec(io_result);
  return 0;
}

/* ---- Argument parsing helpers ---------------------------------------- */

/* Validate that `obj` is a `bytes` of exactly `expected` length. Returns
 * a pointer to its data on success, NULL on failure (and sets an error). */
const uint8_t*
parse_bytes_of_size(
  PyObject* obj,
  Py_ssize_t expected,
  const char* name
) {
  if (!PyBytes_Check(obj)) {
    PyErr_Format(PyExc_TypeError, "%s: expected bytes", name);
    return NULL;
  }
  Py_ssize_t got = PyBytes_GET_SIZE(obj);
  if (got != expected) {
    PyErr_Format(PyExc_ValueError, "%s: expected %zd bytes, got %zd",
                 name, expected, got);
    return NULL;
  }
  return (const uint8_t*) PyBytes_AS_STRING(obj);
}

/* Pack `seq[i]` (each must be `bytes` of `stride`) into a contiguous buffer.
 * Returns malloc'd buffer (caller frees) of size `*out_len * stride`,
 * or NULL on error (sets a Python exception). */
uint8_t*
pack_bytes_sequence(
  PyObject* seq,
  Py_ssize_t stride,
  Py_ssize_t* out_len,
  const char* name
) {
  PyObject* fast = PySequence_Fast(seq, "expected a sequence");
  if (!fast) return NULL;
  Py_ssize_t n = PySequence_Fast_GET_SIZE(fast);
  uint8_t* buf = (uint8_t*) PyMem_Malloc(n * stride);
  if (!buf) {
    Py_DECREF(fast);
    PyErr_NoMemory();
    return NULL;
  }
  for (Py_ssize_t i = 0; i < n; i++) {
    PyObject* item = PySequence_Fast_GET_ITEM(fast, i);
    const uint8_t* p = parse_bytes_of_size(item, stride, name);
    if (!p) { PyMem_Free(buf); Py_DECREF(fast); return NULL; }
    memcpy(buf + i * stride, p, stride);
  }
  Py_DECREF(fast);
  *out_len = n;
  return buf;
}

/* ---- Module table ---------------------------------------------------- */

static PyMethodDef methods[] = {
  {"eth_aggregate_pubkeys", py_eth_aggregate_pubkeys, METH_VARARGS, NULL},
  {"eth_fast_aggregate_verify", py_eth_fast_aggregate_verify, METH_VARARGS, NULL},
  {"blob_to_kzg_commitment", py_blob_to_kzg_commitment, METH_VARARGS, NULL},
  {"compute_challenge", py_compute_challenge, METH_VARARGS, NULL},
  {"compute_kzg_proof", py_compute_kzg_proof, METH_VARARGS, NULL},
  {"verify_kzg_proof", py_verify_kzg_proof, METH_VARARGS, NULL},
  {"compute_blob_kzg_proof", py_compute_blob_kzg_proof, METH_VARARGS, NULL},
  {"verify_blob_kzg_proof", py_verify_blob_kzg_proof, METH_VARARGS, NULL},
  {"verify_blob_kzg_proof_batch", py_verify_blob_kzg_proof_batch, METH_VARARGS, NULL},
  {"compute_cells", py_compute_cells, METH_VARARGS, NULL},
  {"compute_cells_and_kzg_proofs", py_compute_cells_and_kzg_proofs, METH_VARARGS, NULL},
  {"compute_verify_cell_kzg_proof_batch_challenge", py_compute_verify_cell_kzg_proof_batch_challenge, METH_VARARGS, NULL},
  {"verify_cell_kzg_proof_batch", py_verify_cell_kzg_proof_batch, METH_VARARGS, NULL},
  {"recover_cells_and_kzg_proofs", py_recover_cells_and_kzg_proofs, METH_VARARGS, NULL},
  {"xmss_key_gen", py_xmss_key_gen, METH_VARARGS, NULL},
  {"xmss_sign", py_xmss_sign, METH_VARARGS, NULL},
  {"xmss_verify", py_xmss_verify, METH_VARARGS, NULL},
  {"xmss_wots_encode", py_xmss_wots_encode, METH_VARARGS, NULL},
  {"xmss_tweak_hash", py_xmss_tweak_hash, METH_VARARGS, NULL},
  {"xmss_blake2s", py_xmss_blake2s, METH_VARARGS, NULL},
  {NULL, NULL, 0, NULL},
};

static struct PyModuleDef moduledef = {
  PyModuleDef_HEAD_INIT,
  "_native", /* m_name */
  NULL, /* m_doc */
  -1, /* m_size — global state */
  methods,
  NULL, NULL, NULL, NULL,
};

PyMODINIT_FUNC
PyInit__native(void) {
  /* Boot the Lean runtime exactly once when the extension loads. */
  static int initialized = 0;
  if (!initialized) {
    lean_initialize_runtime_module();
    /* Initialize each sub-umbrella; report the first failure if any
     * step errors out. */
    lean_object* res = initialize_EthCryptographySpecs_EthCryptographySpecs_Bls(1);
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
      res = initialize_EthCryptographySpecs_EthCryptographySpecs_Kzg(1);
    }
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
      res = initialize_EthCryptographySpecs_EthCryptographySpecs_Xmss(1);
    }
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
    } else {
      lean_io_result_show_error(res);
      lean_dec(res);
      PyErr_SetString(PyExc_RuntimeError,
                      "failed to initialize Lean runtime");
      return NULL;
    }
    lean_io_mark_end_initialization();

    /* Pull the spec-preset sizes out of the linked Lean static archive */
    BYTES_PER_PUBKEY        = (size_t) eth_bls_const_bytes_per_pubkey(0);
    BYTES_PER_SIGNATURE     = (size_t) eth_bls_const_bytes_per_signature(0);
    BYTES_PER_FIELD_ELEMENT = (size_t) eth_kzg_const_bytes_per_field_element(0);
    BYTES_PER_COMMITMENT    = (size_t) eth_kzg_const_bytes_per_commitment(0);
    BYTES_PER_PROOF         = (size_t) eth_kzg_const_bytes_per_proof(0);
    FIELD_ELEMENTS_PER_BLOB = (size_t) eth_kzg_const_field_elements_per_blob(0);
    BYTES_PER_BLOB          = (size_t) eth_kzg_const_bytes_per_blob(0);
    FIELD_ELEMENTS_PER_CELL = (size_t) eth_kzg_const_field_elements_per_cell(0);
    BYTES_PER_CELL          = (size_t) eth_kzg_const_bytes_per_cell(0);
    CELLS_PER_EXT_BLOB      = (size_t) eth_kzg_const_cells_per_ext_blob(0);
    XMSS_DIGEST_LEN       = (size_t) eth_xmss_const_digest_len(0);
    XMSS_PUBLIC_PARAM_LEN = (size_t) eth_xmss_const_public_param_len(0);
    XMSS_MESSAGE_LEN      = (size_t) eth_xmss_const_message_len(0);
    XMSS_RANDOMNESS_LEN   = (size_t) eth_xmss_const_randomness_len(0);
    XMSS_SEED_LEN         = (size_t) eth_xmss_const_seed_len(0);
    XMSS_CODE_LENGTH      = (size_t) eth_xmss_const_code_length(0);
    XMSS_LOG_LIFETIME     = (size_t) eth_xmss_const_log_lifetime(0);
    XMSS_PUB_KEY_SIZE     = (size_t) eth_xmss_const_pub_key_size(0);
    XMSS_SIG_SIZE         = (size_t) eth_xmss_const_sig_size(0);

    initialized = 1;
  }

  PyObject* m = PyModule_Create(&moduledef);
  if (!m) return NULL;

  /* Expose the spec presets as module-level constants. */
  PyModule_AddIntConstant(m, "BYTES_PER_PUBKEY", BYTES_PER_PUBKEY);
  PyModule_AddIntConstant(m, "BYTES_PER_SIGNATURE", BYTES_PER_SIGNATURE);
  PyModule_AddIntConstant(m, "BYTES_PER_BLOB", BYTES_PER_BLOB);
  PyModule_AddIntConstant(m, "BYTES_PER_FIELD_ELEMENT", BYTES_PER_FIELD_ELEMENT);
  PyModule_AddIntConstant(m, "BYTES_PER_COMMITMENT", BYTES_PER_COMMITMENT);
  PyModule_AddIntConstant(m, "BYTES_PER_PROOF", BYTES_PER_PROOF);
  PyModule_AddIntConstant(m, "FIELD_ELEMENTS_PER_BLOB", FIELD_ELEMENTS_PER_BLOB);
  PyModule_AddIntConstant(m, "FIELD_ELEMENTS_PER_CELL", FIELD_ELEMENTS_PER_CELL);
  PyModule_AddIntConstant(m, "BYTES_PER_CELL", BYTES_PER_CELL);
  PyModule_AddIntConstant(m, "CELLS_PER_EXT_BLOB", CELLS_PER_EXT_BLOB);
  PyModule_AddIntConstant(m, "XMSS_DIGEST_LEN", XMSS_DIGEST_LEN);
  PyModule_AddIntConstant(m, "XMSS_PUBLIC_PARAM_LEN", XMSS_PUBLIC_PARAM_LEN);
  PyModule_AddIntConstant(m, "XMSS_MESSAGE_LEN", XMSS_MESSAGE_LEN);
  PyModule_AddIntConstant(m, "XMSS_RANDOMNESS_LEN", XMSS_RANDOMNESS_LEN);
  PyModule_AddIntConstant(m, "XMSS_SEED_LEN", XMSS_SEED_LEN);
  PyModule_AddIntConstant(m, "XMSS_CODE_LENGTH", XMSS_CODE_LENGTH);
  PyModule_AddIntConstant(m, "XMSS_LOG_LIFETIME", XMSS_LOG_LIFETIME);
  PyModule_AddIntConstant(m, "XMSS_PUB_KEY_SIZE", XMSS_PUB_KEY_SIZE);
  PyModule_AddIntConstant(m, "XMSS_SIG_SIZE", XMSS_SIG_SIZE);
  return m;
}
