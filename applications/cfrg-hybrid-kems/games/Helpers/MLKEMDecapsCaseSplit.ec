(* ==================================================================== *)
(* MLKEMDecapsCaseSplit: ML-KEM's single-key ciphertext-binding           *)
(* predicate, as FIPS 203 decapsulation and as an explicit case analysis  *)
(*                                                                        *)
(* EasyCrypt proof of the ProofFrog zero-advantage helper game pair in    *)
(* the co-located MLKEMDecapsCaseSplit.game.  Both oracles take a         *)
(* decapsulation key's components (dk_PKE, ek, h, z) and two ciphertexts  *)
(* and answer "do they decapsulate to the same shared secret, and do      *)
(* they differ?":                                                          *)
(*                                                                        *)
(*   Left:  decapsulate each ct_i by FIPS 203 Algorithm 18:               *)
(*            m_i = Decrypt(dk_PKE, ct_i);  Kr_i = G(m_i || h);           *)
(*            ss_i = Kr_i[0 : J.Nout];                                    *)
(*            if ct_i != Encrypt(ek, m_i, Kr_i[J.Nout : J.Nout + Nrand])  *)
(*              then ss_i = J(z || ct_i)                                  *)
(*          and return ss0 == ss1 && ct0 != ct1.                          *)
(*   Right: with acc_i = (ct_i == Encrypt(ek, m_i, Kr_i[...])), return    *)
(*            (caseA || caseB0 || caseB1 || caseC) && ct0 != ct1, where   *)
(*            caseA  = !acc0 && !acc1 && J(z || ct0) == J(z || ct1)       *)
(*            caseB0 = !acc0 &&  acc1 && Kr1[0 : J.Nout] == J(z || ct0)   *)
(*            caseB1 =  acc0 && !acc1 && Kr0[0 : J.Nout] == J(z || ct1)   *)
(*            caseC  =  acc0 &&  acc1 && Kr0[0 : J.Nout] == Kr1[0 : J.Nout]*)
(*                                                                        *)
(* The declared bound is 0, and what is proved here is an EQUALITY of     *)
(* probabilities: the two oracles compute the same function, so no        *)
(* distinguisher, whatever it queries, can tell them apart.               *)
(*                                                                        *)
(* Modeling notes.                                                        *)
(*  - Every operation the oracles perform is a deterministic function in  *)
(*    the .game: P.Decrypt, P.Encrypt, G.evaluate and J.evaluate are      *)
(*    declared `deterministic`, and concatenation and slicing are total   *)
(*    functions of their arguments.  Each is an abstract operator here    *)
(*    (Dec, Enc, G, J, catG, catJ, key_half, rand_half) with NO axiom, so *)
(*    the identity is proved for every interpretation of them, a fortiori *)
(*    for the actual K-PKE, SHA3-512, SHAKE256, byte concatenation and    *)
(*    the two slices of G's output.  No property of the lengths or of any *)
(*    primitive is used.                                                  *)
(*  - The two slices of G's output are separate operators: key_half is    *)
(*    Kr[0 : J.Nout] and lands in J's output type (the shared secret,     *)
(*    ss), rand_half is Kr[J.Nout : J.Nout + P.Nrand].  The .game compares *)
(*    a key half with a J output in cases B0 and B1, and the shared type  *)
(*    ss is what makes that comparison well typed here as there.          *)
(*  - The BitString types of the .game are abstract types: dk (P.DecKey), *)
(*    ek (BitString<P.Nek>), hG (the cached hash h), zJ (the rejection    *)
(*    secret z), ct, msg, gin/gout (G's input/output), jin (J's input),   *)
(*    ss and rand.  Nothing about them is used beyond equality.           *)
(*  - Left keeps the .game's statement order and its two `if` blocks that *)
(*    overwrite ss_i on rejection; Right keeps its order of locals.       *)
(*  - The games have no state and no Initialize, so the adversary class   *)
(*    is unrestricted: A may keep any state of its own and call the       *)
(*    oracle any number of times.                                         *)
(*                                                                        *)
(* Proof shape.  The oracle equivalence: on each side, case on the two    *)
(* acceptance flags; in each of the four cases exactly one disjunct of    *)
(* Right is live and it is Left's ss0 == ss1 with the selected values     *)
(* substituted.  The adversary-level equality follows by one `call`.      *)
(* ==================================================================== *)

require import AllCore.

type dk, ek, hG, zJ, ct, msg, gin, gout, jin, ss, rand.

(* P.Decrypt, P.Encrypt, m || h, G.evaluate, the two slices of G's      *)
(* output, z || ct, J.evaluate.                                          *)
op Dec       : dk -> ct -> msg.
op Enc       : ek -> msg -> rand -> ct.
op catG      : msg -> hG -> gin.
op G         : gin -> gout.
op key_half  : gout -> ss.
op rand_half : gout -> rand.
op catJ      : zJ -> ct -> jin.
op J         : jin -> ss.

module type Oracle = {
  proc decide(dk_PKE : dk, ek : ek, h : hG, z : zJ,
              ct0 : ct, ct1 : ct) : bool
}.

module type Adv (O : Oracle) = {
  proc distinguish() : bool {O.decide}
}.

module Left : Oracle = {
  proc decide(dk_PKE : dk, ek : ek, h : hG, z : zJ,
              ct0 : ct, ct1 : ct) : bool = {
    var m0, m1, kr0, kr1, ss0, ss1;
    m0 <- Dec dk_PKE ct0;
    kr0 <- G (catG m0 h);
    ss0 <- key_half kr0;
    if (ct0 <> Enc ek m0 (rand_half kr0)) {
      ss0 <- J (catJ z ct0);
    }
    m1 <- Dec dk_PKE ct1;
    kr1 <- G (catG m1 h);
    ss1 <- key_half kr1;
    if (ct1 <> Enc ek m1 (rand_half kr1)) {
      ss1 <- J (catJ z ct1);
    }
    return ss0 = ss1 /\ ct0 <> ct1;
  }
}.

module Right : Oracle = {
  proc decide(dk_PKE : dk, ek : ek, h : hG, z : zJ,
              ct0 : ct, ct1 : ct) : bool = {
    var m0, m1, kr0, kr1, acc0, acc1, caseA, caseB0, caseB1, caseC;
    m0 <- Dec dk_PKE ct0;
    m1 <- Dec dk_PKE ct1;
    kr0 <- G (catG m0 h);
    kr1 <- G (catG m1 h);
    acc0 <- ct0 = Enc ek m0 (rand_half kr0);
    acc1 <- ct1 = Enc ek m1 (rand_half kr1);
    caseA  <- !acc0 /\ !acc1 /\ J (catJ z ct0) = J (catJ z ct1);
    caseB0 <- !acc0 /\ acc1 /\ key_half kr1 = J (catJ z ct0);
    caseB1 <- acc0 /\ !acc1 /\ key_half kr0 = J (catJ z ct1);
    caseC  <- acc0 /\ acc1 /\ key_half kr0 = key_half kr1;
    return (caseA \/ caseB0 \/ caseB1 \/ caseC) /\ ct0 <> ct1;
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
equiv oracle_eq : Left.decide ~ Right.decide :
  ={arg} ==> ={res}.
proof.
proc.
auto => /> &2.
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
