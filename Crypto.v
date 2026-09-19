(* Long-term asymmetric key material. *)
Parameter public_key  : Type.
Parameter private_key : Type.

(* Ephemeral symmetric key used to encrypt message data. *)
Parameter session_key : Type.

(* Abstract messages and cryptographic objects. *)
Parameter plaintext  : Type.
Parameter ciphertext : Type.
Parameter signature  : Type.

(* ------------------------------------------------------------------ *)
(* Public-key encryption                                               *)
(* ------------------------------------------------------------------ *)

Parameter public_encrypt :
  public_key ->
  plaintext ->
  ciphertext.

Parameter private_decrypt :
  private_key ->
  ciphertext ->
  option plaintext.

Parameter key_pair :
  public_key ->
  private_key ->
  Prop.

Axiom public_key_encryption_correct :
  forall (pk : public_key)
         (sk : private_key)
         (m : plaintext),
    key_pair pk sk ->
    private_decrypt sk (public_encrypt pk m) = Some m.

Parameter encrypted_session_key : Type.

Parameter encrypt_session_key :
  public_key ->
  session_key ->
  encrypted_session_key.

Parameter decrypt_session_key :
  private_key ->
  encrypted_session_key ->
  option session_key.

Axiom session_key_encryption_correct :
  forall (pk : public_key)
         (sk : private_key)
         (k : session_key),
    key_pair pk sk ->
    decrypt_session_key sk (encrypt_session_key pk k) = Some k.

(* ------------------------------------------------------------------ *)
(* Symmetric encryption                                                *)
(* ------------------------------------------------------------------ *)

Parameter symmetric_encrypt :
  session_key ->
  plaintext ->
  ciphertext.

Parameter symmetric_decrypt :
  session_key ->
  ciphertext ->
  option plaintext.

Axiom symmetric_encryption_correct :
  forall (k : session_key)
         (m : plaintext),
    symmetric_decrypt k (symmetric_encrypt k m) = Some m.


