# Summary of theorems for the CFRG hybrid KEM analysis

*Companion to [REPORT-CFRG-20260722.md](REPORT-CFRG-20260722.md), which states the results these theorems establish; see [Section 3.4 of the report](REPORT-CFRG-20260722.md#34-assumptions-and-theorem-bounds) for what we draw from them.*

This document gives the concrete advantage bounds from each of the ProofFrog proofs of the CFRG hybrid KEM combiners.

**Contents**

- [1. How to read these tables](#1-how-to-read-these-tables)
- [2. The assumptions](#2-the-assumptions)
- [3. Correctness](#3-correctness)
- [4. IND-CCA](#4-ind-cca)
- [5. Binding](#5-binding)
- [Appendix A. The statistical facts](#appendix-a-the-statistical-facts)

---

## 1. How to read these tables

Each proof bounds the advantage of an adversary against a particular security property by a sum of advantage terms for each assumption the proof depends on, plus any statistical terms.

Each row in a table summarizes one such bound, with one column per assumption giving the multiplicative factor associated with that assumption's advantage in the theorem's bound. For example, the following row of the binding table of [Section 5](#5-binding)

| Scheme | Result | Notion | KEM_PQ bind | KDF cr | PRG sec. | KGE KEM_PQ | KGE KEM_T | Statistical | RO? |
|---|---|---|---|---|---|---|---|---|---|
| CG seeded | LEAK | K-PK | a | b | c | d | e | f | G |

corresponds to the advantage bound

```
Adv^{LEAK-BIND-K-PK}_{CG-seeded}(A)
    <=  a * Adv^{LEAK-BIND-K-PK}_{KEM_PQ}(B1)
      + b * Adv^{CollisionResistance}_{KDF}(B2)
      + c * Adv^{PRGSec}_{PRG}(B3)
      + d * Adv^{KeyGenEquiv}_{KEM_PQ}(B4)
      + e * Adv^{KeyGenEquiv}_{KEM_T}(B5)
      + f
```

where the superscript is the assumption game of [Section 2](#2-the-assumptions), the subscript is what it is assumed of, and `B1` to `B5` are the reductions the proof constructs from the adversary `A`. A blank cell is zero, and a coefficient greater than one collects that many separate reductions of the same kind, which the `bound:` clause lists individually.

For this particular example, the row actually is

| Scheme | Result | Notion | KEM_PQ bind | KDF cr | PRG sec. | KGE KEM_PQ | KGE KEM_T | Statistical | RO? | Proof |
|---|---|---|---|---|---|---|---|---|---|---|
| CG seeded | LEAK | K-PK | 1 | 1 |  | 2 |  | 2^(1-λ) | G | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_LEAK_BIND_K_PK.proof) |

so the ProofFrog proof [`CG_seedbased_LEAK_BIND_K_PK`](proofs/CG/CG_seedbased_LEAK_BIND_K_PK.proof) establishes the bound

```
Adv^{LEAK-BIND-K-PK}_{CG-seeded}(A)
    <=  Adv^{LEAK-BIND-K-PK}_{KEM_PQ}(B1)
      + Adv^{CollisionResistance}_{KDF}(B2)
      + 2 * Adv^{KeyGenEquiv}_{KEM_PQ}(B4)
      + 2^(1-λ)
```

with the seed expansion modelled as a random oracle, which is what the `G` in the **RO?** column records.

The following columns are interpreted as follows:

- **KGE** counts terms for the `KeyGenEquiv` seed-to-expanded bridge, one column per component KEM. Its game declares no advantage bound, so the bridge appears as an ordinary term rather than a free step; see [Section 2](#2-the-assumptions). A bridged component contributes two terms, distinguished by the `_L` and `_R` suffixes on their reductions, so these cells read 2 where the component is bridged and blank where it is not.
- **Statistical** gives the additive unconditional loss, as distinct from the advantage terms counted by the other columns. These come from the random-oracle reprogramming facts of [Appendix A](#appendix-a-the-statistical-facts), and the column appears only in the binding table; the random-oracle fact used in the IND-CCA proofs yields identical distributions and thus contribute 0 to the bound.
- **RO?** indicates which primitives, if any, are modelled as a random oracle: `H` for the combiner KDF, `G` for the seed-expander PRG, or `std` for a standard-model result.

---

## 2. The assumptions

### 2.1. Cryptographic assumptions

| Column | Assumption | Game |
|---|---|---|
| KEM_PQ corr., KEM_T corr. | A component KEM decapsulates to the shared secret it encapsulated | [`Correctness`](games/KEM/Correctness.game) |
| KEM_PQ corr-dk, KEM_T corr-dk | Correctness as above, with the extension that it gives the correctness adversary the decapsulation key (which an IND-CCA reduction needs in order to answer `Decaps` queries) | [`CorrectnessWithDK`](games/KEM/CorrectnessWithDK.game) |
| KEM_PQ cca | IND-CCA security of the post-quantum KEM | [`INDCCA`](games/KEM/INDCCA.game) |
| KEM_T cca | IND-CCA security of the traditional KEM | [`INDCCA`](games/KEM/INDCCA.game) |
| KEM_PQ c2pri | Ciphertext second preimage resistant: Given an honest key pair, its decapsulation key, and a challenge ciphertext, it is hard to find a second ciphertext decapsulating to the same shared secret | [`C2PRI`](games/KEM/C2PRI.game) |
| KEM_PQ bind | LEAK-BIND or HON-BIND of the post-quantum KEM (specifically the same as whichever of the K-CT-DIFFKEY, K-CT-SAMEKEY and K-PK notions the row proves) | [`games/KEM/Binding/`](games/KEM/Binding/) |
| NG corr. | Exponentiation in the nominal group commutes, so the two parties derive the same element | [`NGCorrectness`](games/Group/NGCorrectness.game) |
| NG sdh | Strong Diffie-Hellman with both the target and the decision oracle over shared-secret encodings rather than group elements; see [Finding F2 of the report](REPORT-CFRG-20260722.md#f2-the-traditional-branches-of-ug-and-cg-depend-on-a-variant-of-sdh-over-shared-secret-encodings-not-group-elements) | [`SDH_SS`](games/Group/SDH_SS.game) |
| NG rsd | Scalars derived from a uniform seed are indistinguishable from uniform scalars | [`RandomScalarDist`](games/Group/RandomScalarDist.game) |
| KDF cr | Collision resistance of the combiner KDF | [`KDFCollisionResistance`](games/KDF/KDFCollisionResistance.game) |
| KDF prf | The KDF is a PRF on its single key input | [`KDFPRFSec`](games/KDF/KDFPRFSec.game) |
| KDF 1prf | The split-key KDF is a PRF on its first key input, `ss_PQ` | [`KDFFirstKeyPRF`](games/KDF/KDFFirstKeyPRF.game) |
| KDF 2prf | The split-key KDF is a PRF on its second key input, `ss_T` | [`KDFSecondKeyPRF`](games/KDF/KDFSecondKeyPRF.game) |
| PRG sec. | The seed expansion is a secure pseudorandom generator | [`PRGSec`](games/PRG/PRGSec.game) |

### 2.2. KeyGenEquiv: bridging from seed to expanded key derivation

[`KeyGenEquiv`](games/KEM/KeyGenEquiv.game) asserts that `KeyGen()` is distributionally equivalent to `[s <- BitString<Nseed>; DeriveKeyPair(s)]`. Every seed-form proof invokes it once per component KEM, immediately after `PRGSec`, to convert `DeriveKeyPair(uniform seed)` into the `KeyGen()` form in which the component assumption games are stated.

The engine does not treat the bridge as free/statistical, so it appears explicitly in each advantage bound, for each of the underlying KEMs; these are the columns **KGE KEM_PQ** and **KGE KEM_T**.

Nonetheless, this is not necessarily a cryptographic assumption. It does hold for the KEMs that draft -12 targets, such as ML-KEM, which specifies key generation as sampling a pair of values and invoking a deterministic internal routine on them. But it is not vacuous in general, and it is a requirement on the components that draft -12 does not state. See [Finding F3 of the report](REPORT-CFRG-20260722.md#f3-the-seed-based-analyses-repeatedly-assume-that-generatekeypair-is-equivalent-to-derivekeypair-on-a-random-seed).

We need the bridge in part because we chose to model the security games in terms of a KEM's key generation algorithm, following the natural convention in the literature, rather than sampling a seed and calling `DeriveKeyPair`. The seed-form LEAK-BIND proofs are the exceptions, and they differ from each other: those for UG and UK use neither half of the bridge, since their bound is a single KDF collision term and the seed plays no role in the argument, whereas those for CG and CK invoke `KeyGenEquiv` on `KEM_PQ` but not `PRGSec`, because the adversary is given the seed and the seed expansion is modelled as a random oracle instead; see [Finding F1 of the report](REPORT-CFRG-20260722.md#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model).

---

## 3. Correctness

| Scheme | KEM_PQ corr. | KEM_T corr. | NG corr. | PRG sec. | KGE KEM_PQ | KGE KEM_T | RO? | Proof |
|---|---|---|---|---|---|---|---|---|
| CG seeded | 1 |  | 1 | 2 | 2 |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_Correctness.proof) |
| CG expanded | 1 |  | 1 |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_expanded_Correctness.proof) |
| CK seeded | 1 | 1 |  | 2 | 2 | 2 | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_seedbased_Correctness.proof) |
| CK expanded | 1 | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_expanded_Correctness.proof) |
| UG seeded | 1 |  | 1 | 2 | 2 |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_seedbased_Correctness.proof) |
| UG expanded | 1 |  | 1 |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_expanded_Correctness.proof) |
| UK seeded | 1 | 1 |  | 2 | 2 | 2 | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_seedbased_Correctness.proof) |
| UK expanded | 1 | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_expanded_Correctness.proof) |

Correctness of the expanded schemes depends only on correctness of the components: the two component KEMs for UK and CK, and the component KEM and the nominal group for UG and CG. The seed-form schemes additionally depend on `PRG sec.` and on the `KeyGenEquiv` bridge, because both component key pairs are derived from the single hybrid seed whereas the component correctness assumptions are stated with respect to each component's own key generation. A correctness theorem relying on a computational assumption is unusual, so it is worth noting.

## 4. IND-CCA

| Scheme | Branch | KEM_PQ corr-dk | KEM_PQ cca | KEM_PQ c2pri | KEM_T corr-dk | KEM_T cca | NG sdh | NG rsd | KDF 1prf | KDF 2prf | KDF prf | PRG sec. | KGE KEM_PQ | KGE KEM_T | RO? | Proof |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| CG seeded | PQ | 2 | 2 |  |  |  |  |  |  |  | 2 | 2 | 2 |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_INDCCA_PQ.proof) |
| CG seeded | T |  |  | 2 |  |  | 1 | 2 |  |  |  | 2 | 2 |  | H | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_INDCCA_T.proof) |
| CG expanded | PQ | 2 | 2 |  |  |  |  |  |  |  | 2 |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_expanded_INDCCA_PQ.proof) |
| CG expanded | T |  |  | 2 |  |  | 1 | 2 |  |  |  |  |  |  | H | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_expanded_INDCCA_T.proof) |
| CK seeded | PQ | 2 | 2 |  |  |  |  |  | 2 |  |  | 2 | 2 | 2 | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_seedbased_INDCCA_PQ.proof) |
| CK seeded | T |  |  | 2 | 2 | 2 |  |  |  | 2 |  | 2 | 2 | 2 | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_seedbased_INDCCA_T.proof) |
| CK expanded | PQ | 2 | 2 |  |  |  |  |  | 2 |  |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_expanded_INDCCA_PQ.proof) |
| CK expanded | T |  |  | 2 | 2 | 2 |  |  |  | 2 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_expanded_INDCCA_T.proof) |
| UG seeded | PQ | 2 | 2 |  |  |  |  |  |  |  | 2 | 2 | 2 |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_seedbased_INDCCA_PQ.proof) |
| UG seeded | T |  |  |  |  |  | 1 | 2 |  |  |  | 2 | 2 |  | H | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_seedbased_INDCCA_T.proof) |
| UG expanded | PQ | 2 | 2 |  |  |  |  |  |  |  | 2 |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_expanded_INDCCA_PQ.proof) |
| UG expanded | T |  |  |  |  |  | 1 | 2 |  |  |  |  |  |  | H | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_expanded_INDCCA_T.proof) |
| UK seeded | PQ | 2 | 2 |  |  |  |  |  | 2 |  |  | 2 | 2 | 2 | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_seedbased_INDCCA_PQ.proof) |
| UK seeded | T |  |  |  | 2 | 2 |  |  |  | 2 |  | 2 | 2 | 2 | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_seedbased_INDCCA_T.proof) |
| UK expanded | PQ | 2 | 2 |  |  |  |  |  | 2 |  |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_expanded_INDCCA_PQ.proof) |
| UK expanded | T |  |  |  | 2 | 2 |  |  |  | 2 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_expanded_INDCCA_T.proof) |

The traditional branches of UG and CG are the only IND-CCA results outside the standard model, and the only ones that use `NG sdh` and `NG rsd`.

`KEM_PQ c2pri` appears in exactly the four traditional-branch proofs for CG and CK, which is the property the C2PRI combiner is named after. These four proofs are the only ones that cite `C2PRI` in a `bound:` clause; in particular, no binding proof does.

All eight post-quantum branches assume the KDF is a pseudorandom function keyed on `ss_PQ`, which sits at the start of the KDF input. The UG and CG proofs use the usual single-key PRF formulation (`KDF prf`), whereas UK and CK use the split-key PRF formulation, keyed on the first key (`KDF 1prf`), which differs in also letting the adversary choose `ss_T`. The traditional branches of UK and CK assume the split-key PRF formulation keyed on `ss_T` instead (`KDF 2prf`). The traditional branches of UG and CG assume no PRF property of the KDF at all, which is why their four KDF cells are blank; they model the KDF as a random oracle instead.

## 5. Binding

| Scheme | Result | Notion | KEM_PQ bind | KDF cr | PRG sec. | KGE KEM_PQ | KGE KEM_T | Statistical | RO? | Proof |
|---|---|---|---|---|---|---|---|---|---|---|
| CG seeded | LEAK | K-CT-DIFFKEY | 1 | 1 |  | 2 |  | 2^(1-λ) | G | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_LEAK_BIND_K_CT_DIFFKEY.proof) |
| CG seeded | LEAK | K-CT-SAMEKEY | 1 | 1 |  | 2 |  |  | G | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_LEAK_BIND_K_CT_SAMEKEY.proof) |
| CG seeded | LEAK | K-PK | 1 | 1 |  | 2 |  | 2^(1-λ) | G | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_LEAK_BIND_K_PK.proof) |
| CG seeded | HON | K-CT-DIFFKEY | 1 | 1 | 2 | 2 |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_HON_BIND_K_CT_DIFFKEY.proof) |
| CG seeded | HON | K-CT-SAMEKEY | 1 | 1 | 2 | 2 |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_HON_BIND_K_CT_SAMEKEY.proof) |
| CG seeded | HON | K-PK | 1 | 1 | 2 | 2 |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_seedbased_HON_BIND_K_PK.proof) |
| CG expanded | LEAK | K-CT-DIFFKEY | 1 | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_expanded_LEAK_BIND_K_CT_DIFFKEY.proof) |
| CG expanded | LEAK | K-CT-SAMEKEY | 1 | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_expanded_LEAK_BIND_K_CT_SAMEKEY.proof) |
| CG expanded | LEAK | K-PK | 1 | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CG/CG_expanded_LEAK_BIND_K_PK.proof) |
| CK seeded | LEAK | K-CT-DIFFKEY | 1 | 1 |  | 2 |  | 2^(1-λ) | G | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_seedbased_LEAK_BIND_K_CT_DIFFKEY.proof) |
| CK seeded | LEAK | K-CT-SAMEKEY | 1 | 1 |  | 2 |  |  | G | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_seedbased_LEAK_BIND_K_CT_SAMEKEY.proof) |
| CK seeded | LEAK | K-PK | 1 | 1 |  | 2 |  | 2^(1-λ) | G | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_seedbased_LEAK_BIND_K_PK.proof) |
| CK seeded | HON | K-CT-DIFFKEY | 1 | 1 | 2 | 2 | 2 |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_seedbased_HON_BIND_K_CT_DIFFKEY.proof) |
| CK seeded | HON | K-CT-SAMEKEY | 1 | 1 | 2 | 2 | 2 |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_seedbased_HON_BIND_K_CT_SAMEKEY.proof) |
| CK seeded | HON | K-PK | 1 | 1 | 2 | 2 | 2 |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_seedbased_HON_BIND_K_PK.proof) |
| CK expanded | LEAK | K-CT-DIFFKEY | 1 | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_expanded_LEAK_BIND_K_CT_DIFFKEY.proof) |
| CK expanded | LEAK | K-CT-SAMEKEY | 1 | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_expanded_LEAK_BIND_K_CT_SAMEKEY.proof) |
| CK expanded | LEAK | K-PK | 1 | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/CK/CK_expanded_LEAK_BIND_K_PK.proof) |
| UG seeded | LEAK | K-CT-DIFFKEY |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_seedbased_LEAK_BIND_K_CT_DIFFKEY.proof) |
| UG seeded | LEAK | K-CT-SAMEKEY |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_seedbased_LEAK_BIND_K_CT_SAMEKEY.proof) |
| UG seeded | LEAK | K-PK |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_seedbased_LEAK_BIND_K_PK.proof) |
| UG expanded | LEAK | K-CT-DIFFKEY |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_expanded_LEAK_BIND_K_CT_DIFFKEY.proof) |
| UG expanded | LEAK | K-CT-SAMEKEY |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_expanded_LEAK_BIND_K_CT_SAMEKEY.proof) |
| UG expanded | LEAK | K-PK |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UG/UG_expanded_LEAK_BIND_K_PK.proof) |
| UK seeded | LEAK | K-CT-DIFFKEY |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_seedbased_LEAK_BIND_K_CT_DIFFKEY.proof) |
| UK seeded | LEAK | K-CT-SAMEKEY |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_seedbased_LEAK_BIND_K_CT_SAMEKEY.proof) |
| UK seeded | LEAK | K-PK |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_seedbased_LEAK_BIND_K_PK.proof) |
| UK expanded | LEAK | K-CT-DIFFKEY |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_expanded_LEAK_BIND_K_CT_DIFFKEY.proof) |
| UK expanded | LEAK | K-CT-SAMEKEY |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_expanded_LEAK_BIND_K_CT_SAMEKEY.proof) |
| UK expanded | LEAK | K-PK |  | 1 |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/UK/UK_expanded_LEAK_BIND_K_PK.proof) |
| Generic (LEAK => HON) | - | K-CT-DIFFKEY | 1 |  |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/Generic/LEAK_implies_HON_BIND_K_CT_DIFFKEY.proof) |
| Generic (LEAK => HON) | - | K-CT-SAMEKEY | 1 |  |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/Generic/LEAK_implies_HON_BIND_K_CT_SAMEKEY.proof) |
| Generic (LEAK => HON) | - | K-PK | 1 |  |  |  |  |  | std | [proof](https://github.com/ProofFrog/examples/blob/main/applications/cfrg-hybrid-kems/proofs/Generic/LEAK_implies_HON_BIND_K_PK.proof) |

Every UG and UK binding proof relies on `KDF cr` alone, with no assumption at all on the component KEMs: the universal combiners include `ct_PQ` and `ek_PQ` in the KDF input, so two distinct ciphertexts or encapsulation keys yielding the same hybrid shared secret give a KDF collision directly. The C2PRI combiners omit the post-quantum KEM's ciphertext and encapsulation key from the KDF input, so the proof must instead depend on the binding of the post-quantum component, which is why every CG and CK row includes a `KEM_PQ bind` term. The three generic rows use only the LEAK-BIND assumption they reduce from.

Among the seed-form CG and CK proofs, the HON-BIND rows use `PRG sec.` and are standard-model results, whereas the LEAK-BIND rows use no `PRG sec.` at all, carry a statistical term, and are the only results anywhere in this document that model the seed expansion as a random oracle. That contrast is discussed in [Finding F1 of the report](REPORT-CFRG-20260722.md#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model).

---

## Appendix A. The statistical facts

Six games in [`games/ROM/`](games/ROM/) are not assumptions about a primitive but unconditional facts about reprogramming a random oracle, used to justify steps that would otherwise not go through. (ProofFrog justifies a game hop in only two ways: the two games canonicalize to the same thing, or the hop is a reduction to a pair of games assumed indistinguishable. There is no way to state directly that two games differ by at most some quantity, so a statistical step has to be written as a game pair like any assumption.) What sets these six apart is that a concrete bound can be externally derived and included in the game file to then be accumulated into the advantage. Those declared bounds are summed into the **Statistical** column, and a fact whose bound is zero therefore leaves no trace in the tables.

| Fact | Game | Declared bound | EasyCrypt proof | Used by |
|---|---|---|---|---|
| **One point.** A seed is sampled and given to the adversary. Answering its hash query at that seed with an independently sampled value is the same as answering it with the oracle, since the oracle's value at a fresh point is uniform and independent of everything else the adversary sees. This is what lets a proof plant a challenge in the seed expansion at one point. | [`LazyROOneSeeded`](games/ROM/LazyROOneSeeded.game), [`CGLazyROOneSeeded`](games/ROM/CGLazyROOneSeeded.game) | 0 (exact) | [`LazyROOneSeeded.ec`](games/ROM/LazyROOneSeeded.ec), [`CGLazyROOneSeeded.ec`](games/ROM/CGLazyROOneSeeded.ec) | seed-form CG / CK LEAK-BIND-K-CT-SAMEKEY |
| **Two points.** The same with two seeds, needed when a proof plants a challenge at each of two seeds. The two games differ only when the two independently sampled seeds happen to collide, which is where the bound comes from. | [`LazyROTwoSeeded`](games/ROM/LazyROTwoSeeded.game), [`CGLazyROTwoSeeded`](games/ROM/CGLazyROTwoSeeded.game) | 2^-λ | [`LazyROTwoSeeded.ec`](games/ROM/LazyROTwoSeeded.ec), [`CGLazyROTwoSeeded.ec`](games/ROM/CGLazyROTwoSeeded.ec) | seed-form CG / CK LEAK-BIND-K-CT-DIFFKEY and K-PK |
| **Two views.** One oracle is reached two ways, directly and through an injective packing of a query and some state. Answering the two from separate lazy tables is the same as answering both from one random function, because injectivity of the packing means an entry of one view can alias an entry of the other only where the two genuinely coincide. | [`LazyROTwoViewsExcluded`](games/ROM/LazyROTwoViewsExcluded.game), [`LazyROTwoViewsExcludedProgrammed`](games/ROM/LazyROTwoViewsExcludedProgrammed.game) | 0 (exact) | [`LazyROTwoViewsExcluded.ec`](games/ROM/LazyROTwoViewsExcluded.ec), [`LazyROTwoViewsExcludedProgrammed.ec`](games/ROM/LazyROTwoViewsExcludedProgrammed.ec) | UG / CG T-branch IND-CCA |

**Checking the declared bounds in EasyCrypt.** Each of the six has an EasyCrypt proof of the bound it declares, written directly (by an LLM) rather than produced by ProofFrog's EasyCrypt exporter. For the two-point helpers the proof establishes the declared inequality, bounding the distinguishing probability by one over the size of the seed space. For the one-point helpers it establishes the stronger claim of zero statistical distance. The CG variants are proved from the same generic EasyCrypt theories as the two-KEM ones, since in both cases the two halves of the codomain are abstract types carrying arbitrary distributions, so one theorem covers the two-KEM and the KEM-and-group instantiations.

These proofs are admit-free but not axiom-free. The two-point proofs assume that the seed space has more than one element and that the two component seed distributions are lossless, and the two-view proofs assume that the packing function is injective; these are hypotheses on the instantiation rather than gaps in the argument. The one-point proofs assume only losslessness of the two component distributions, and nothing at all about the seed distribution, which is an arbitrary distribution on an abstract type; nor is the adversary constrained to be lossless or to make boundedly many queries, so those results hold without a query bound.
