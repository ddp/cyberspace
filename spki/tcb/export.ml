(** SPKI TCB - C API Export for Chicken Scheme FFI
 *
 * Exports OCaml TCB functions to C so they can be called from Chicken Scheme.
 * This is the boundary between the verified OCaml TCB and the Scheme policy layer.
 *
 * Architecture:
 *   Chicken Scheme → C FFI → export.ml → signature.ml → libsodium
 *
 * All functions are exposed with C linkage for Scheme FFI.
 *)

(** Initialize the TCB - MUST be called before any crypto operations
 * Returns: 0 on success, -1 on failure
 *)
let tcb_init () =
  try
    Signature.init ();
    0
  with _ -> -1

(** Generate Ed25519 keypair
 * @param public_key_out: buffer for 32-byte public key
 * @param secret_key_out: buffer for 64-byte secret key
 * @return 0 on success, -1 on failure
 *
 * Caller must provide pre-allocated buffers of correct size.
 *)
let tcb_keypair_generate public_key_out secret_key_out =
  try
    let keypair = Signature.generate_keypair () in
    Bytes.blit keypair.public_key 0 public_key_out 0 32;
    Bytes.blit keypair.secret_key 0 secret_key_out 0 64;
    0
  with _ -> -1

(** Sign message with Ed25519
 * @param secret_key: 64-byte secret key
 * @param message: message to sign
 * @param message_len: length of message
 * @param signature_out: buffer for 64-byte signature
 * @return 0 on success, -1 on failure
 *)
let tcb_sign secret_key message message_len signature_out =
  try
    let msg_bytes = Bytes.create message_len in
    Bytes.blit message 0 msg_bytes 0 message_len;
    let signature = Signature.sign secret_key msg_bytes in
    Bytes.blit signature 0 signature_out 0 64;
    0
  with _ -> -1

(** Verify Ed25519 signature
 * @param public_key: 32-byte public key
 * @param message: message that was signed
 * @param message_len: length of message
 * @param signature: 64-byte signature
 * @return 1 if valid, 0 if invalid, -1 on error
 *
 * TCB CRITICAL: This is the core security guarantee.
 * If this returns 1, the signature was created by holder of the private key.
 *)
let tcb_verify public_key message message_len signature =
  try
    let msg_bytes = Bytes.create message_len in
    Bytes.blit message 0 msg_bytes 0 message_len;
    let valid = Signature.verify public_key msg_bytes signature in
    if valid then 1 else 0
  with _ -> -1

(** Hash data with SHA-256
 * @param data: data to hash
 * @param data_len: length of data
 * @param hash_out: buffer for 32-byte hash
 * @return 0 on success, -1 on failure
 *)
let tcb_hash data data_len hash_out =
  try
    let data_bytes = Bytes.create data_len in
    Bytes.blit data 0 data_bytes 0 data_len;
    let hash = Signature.hash data_bytes in
    Bytes.blit hash 0 hash_out 0 32;
    0
  with _ -> -1

(**
 * Export all functions with C linkage for Chicken Scheme FFI
 *)

let () = Callback.register "tcb_init" tcb_init
let () = Callback.register "tcb_keypair_generate" tcb_keypair_generate
let () = Callback.register "tcb_sign" tcb_sign
let () = Callback.register "tcb_verify" tcb_verify
let () = Callback.register "tcb_hash" tcb_hash

(**
 * TCB C API Summary:
 *
 * int tcb_init(void)
 * int tcb_keypair_generate(unsigned char *pk, unsigned char *sk)
 * int tcb_sign(unsigned char *sk, unsigned char *msg, int len, unsigned char *sig)
 * int tcb_verify(unsigned char *pk, unsigned char *msg, int len, unsigned char *sig)
 * int tcb_hash(unsigned char *data, int len, unsigned char *hash)
 *
 * All functions return 0 on success, -1 on error (except verify: 1=valid, 0=invalid, -1=error)
 *)
