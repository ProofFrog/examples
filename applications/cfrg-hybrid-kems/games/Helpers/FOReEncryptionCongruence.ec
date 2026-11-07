(* ==================================================================== *)
(* FOReEncryptionCongruence: distinct ciphertexts that both pass the      *)
(* Fujisaki-Okamoto re-encryption check come from distinct messages       *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog zero-advantage helper game pair in    *)
(* the co-located FOReEncryptionCongruence.game:                          *)
(*                                                                        *)
(*   Left.BothReEncrypt(ek, h, m0, m1, ct0, ct1) returns                  *)
(*       ct0 != ct1                                                       *)
(*       && ct0 == Encrypt(ek, m0, G(m0 || h)[ntrunc : ntrunc + Nrand])    *)
(*       && ct1 == Encrypt(ek, m1, G(m1 || h)[ntrunc : ntrunc + Nrand])    *)
(*   Right.BothReEncrypt(...) returns the same conjunction && m0 != m1     *)
(*                                                                        *)
(* The declared bound is 0, and what is proved here is an EQUALITY of     *)
(* probabilities: the two oracles compute the same function, so no        *)
(* distinguisher, whatever it queries, can tell them apart.               *)
(*                                                                        *)
(* Modeling notes.                                                        *)
(*  - Every operation the oracles perform is a deterministic function in  *)
(*    the .game: P.Encrypt and G.evaluate are declared `deterministic`,   *)
(*    and concatenation and slicing are total functions of their          *)
(*    arguments.  Each is an abstract operator here (Enc, G, catG,        *)
(*    rand_half) with NO axiom, so the identity is proved for every       *)
(*    interpretation of them, a fortiori for the actual DetPKE, SHA3-512, *)
(*    byte concatenation and the [ntrunc : ntrunc + Nrand] slice.  The    *)
(*    proof uses only that each is a function (congruence); it uses no    *)
(*    property of ntrunc, of the lengths, or of any primitive.            *)
(*  - The BitString types of the .game are abstract types: ek (the        *)
(*    BitString<P.Nek> encapsulation key), hG (the cached public-key      *)
(*    hash h, BitString<G.Nin - P.Nmsg>), msg, ct, gin (G's input),       *)
(*    gout (G's output) and rand (the encryption coins).  Nothing about   *)
(*    them is used beyond equality.                                       *)
(*  - The games have no state and no Initialize, so the adversary class   *)
(*    is unrestricted: A may keep any state of its own and call the       *)
(*    oracle any number of times.                                         *)
(*                                                                        *)
(* Proof shape.  The oracle equivalence: if m0 = m1 then the two          *)
(* re-encryption calls have equal arguments, hence equal results, so the  *)
(* second and third conjuncts give ct0 = ct1, contradicting the first;    *)
(* hence the added conjunct m0 <> m1 is redundant.  The adversary-level   *)
(* equality follows by one `call`.                                         *)
(* ==================================================================== *)

require import AllCore.

type ek, hG, msg, ct, gin, gout, rand.

(* m || h, G.evaluate, the coins slice of G's output, P.Encrypt. *)
op catG      : msg -> hG -> gin.
op G         : gin -> gout.
op rand_half : gout -> rand.
op Enc       : ek -> msg -> rand -> ct.

module type Oracle = {
  proc bothReEncrypt(ek : ek, h : hG, m0 : msg, m1 : msg,
                     ct0 : ct, ct1 : ct) : bool
}.

module type Adv (O : Oracle) = {
  proc distinguish() : bool {O.bothReEncrypt}
}.

module Left : Oracle = {
  proc bothReEncrypt(ek : ek, h : hG, m0 : msg, m1 : msg,
                     ct0 : ct, ct1 : ct) : bool = {
    return ct0 <> ct1
        /\ ct0 = Enc ek m0 (rand_half (G (catG m0 h)))
        /\ ct1 = Enc ek m1 (rand_half (G (catG m1 h)));
  }
}.

module Right : Oracle = {
  proc bothReEncrypt(ek : ek, h : hG, m0 : msg, m1 : msg,
                     ct0 : ct, ct1 : ct) : bool = {
    return ct0 <> ct1
        /\ ct0 = Enc ek m0 (rand_half (G (catG m0 h)))
        /\ ct1 = Enc ek m1 (rand_half (G (catG m1 h)))
        /\ m0 <> m1;
  }
}.

module Game (A : Adv) (O : Oracle) = {
  proc main() : bool = {
    var b;
    b <@ A(O).distinguish();
    return b;
  }
}.

(* The two oracles compute the same function. *)
equiv oracle_eq : Left.bothReEncrypt ~ Right.bothReEncrypt :
  ={arg} ==> ={res}.
proof.
proc; skip => /> &2.
smt().
qed.

section PROOF.

declare module A <: Adv.

(* The advantage: exactly 0, for every predicate P on A's output. *)
lemma adv_bound &m (P : bool -> bool) :
  Pr[Game(A, Left).main() @ &m : P res]
  = Pr[Game(A, Right).main() @ &m : P res].
proof.
byequiv (: ={glob A} ==> ={res}) => //.
proc.
call (: true).
+ by conseq oracle_eq => /#.
by auto.
qed.

end section PROOF.
