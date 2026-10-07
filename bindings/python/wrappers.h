/*
 * Shared declarations for the EthCryptographySpecs CPython extension.
 *
 * `module.c` defines `PyInit__native`, the method table, the spec-size
 * globals, and the marshalling helpers.
 */
#ifndef ETHCS_WRAPPERS_H
#define ETHCS_WRAPPERS_H

#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

/* ---- Spec sizes (initialized in `PyInit__native`) -------------------- */

extern size_t BYTES_PER_PUBKEY;
extern size_t BYTES_PER_SIGNATURE;

extern size_t BYTES_PER_FIELD_ELEMENT;
extern size_t BYTES_PER_COMMITMENT;
extern size_t BYTES_PER_PROOF;
extern size_t FIELD_ELEMENTS_PER_BLOB;
extern size_t BYTES_PER_BLOB;
extern size_t FIELD_ELEMENTS_PER_CELL;
extern size_t BYTES_PER_CELL;
extern size_t CELLS_PER_EXT_BLOB;

extern size_t XMSS_DIGEST_LEN;
extern size_t XMSS_PUBLIC_PARAM_LEN;
extern size_t XMSS_MESSAGE_LEN;
extern size_t XMSS_RANDOMNESS_LEN;
extern size_t XMSS_SEED_LEN;
extern size_t XMSS_CODE_LENGTH;
extern size_t XMSS_LOG_LIFETIME;
extern size_t XMSS_PUB_KEY_SIZE;
extern size_t XMSS_SIG_SIZE;

/* ---- Lean ↔ C marshalling helpers ------------------------------------ */

lean_object*
mk_bytearray(
  const uint8_t* data,
  size_t len
);

lean_object*
mk_bytearray_array(
  const uint8_t* data,
  size_t n,
  size_t stride
);

int
run_io_into_bytearray(
  lean_object* io_result,
  uint8_t* out,
  size_t out_len
);

int
run_io_into_bool(
  lean_object* io_result,
  uint8_t* out_ok
);

/* ---- Argument parsing helpers ---------------------------------------- */

const uint8_t*
parse_bytes_of_size(
  PyObject* obj,
  Py_ssize_t expected,
  const char* name
);

uint8_t*
pack_bytes_sequence(
  PyObject* seq,
  Py_ssize_t stride,
  Py_ssize_t* out_len,
  const char* name
);

/* ---- Wrapper functions ----------------------------------------------- */

PyObject* py_eth_aggregate_pubkeys                        (PyObject* self, PyObject* args);
PyObject* py_eth_fast_aggregate_verify                    (PyObject* self, PyObject* args);

PyObject* py_blob_to_kzg_commitment                       (PyObject* self, PyObject* args);
PyObject* py_compute_challenge                            (PyObject* self, PyObject* args);
PyObject* py_compute_kzg_proof                            (PyObject* self, PyObject* args);
PyObject* py_verify_kzg_proof                             (PyObject* self, PyObject* args);
PyObject* py_compute_blob_kzg_proof                       (PyObject* self, PyObject* args);
PyObject* py_verify_blob_kzg_proof                        (PyObject* self, PyObject* args);
PyObject* py_verify_blob_kzg_proof_batch                  (PyObject* self, PyObject* args);
PyObject* py_compute_cells                                (PyObject* self, PyObject* args);
PyObject* py_compute_cells_and_kzg_proofs                 (PyObject* self, PyObject* args);
PyObject* py_compute_verify_cell_kzg_proof_batch_challenge(PyObject* self, PyObject* args);
PyObject* py_verify_cell_kzg_proof_batch                  (PyObject* self, PyObject* args);
PyObject* py_recover_cells_and_kzg_proofs                 (PyObject* self, PyObject* args);

PyObject* py_xmss_key_gen                                 (PyObject* self, PyObject* args);
PyObject* py_xmss_sign                                    (PyObject* self, PyObject* args);
PyObject* py_xmss_verify                                  (PyObject* self, PyObject* args);
PyObject* py_xmss_wots_encode                             (PyObject* self, PyObject* args);
PyObject* py_xmss_tweak_hash                              (PyObject* self, PyObject* args);
PyObject* py_xmss_blake2s                                 (PyObject* self, PyObject* args);

#endif /* ETHCS_WRAPPERS_H */
