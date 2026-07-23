# A machine-checked analysis of the four hybrid KEM combiners of draft-irtf-cfrg-hybrid-kems: comments for the IRTF CFRG working group last call

**Douglas Stebila and Camryn Steckel**, University of Waterloo

*July 22, 2026.*

---

## Contents

- [1. Summary](#1-summary)
- [2. Draft -10 versus draft -12](#2-draft--10-versus-draft--12)
- [3. Provable security analysis](#3-provable-security-analysis)
- [4. Findings and suggested changes](#4-findings-and-suggested-changes)
- [5. Scope and caveats](#5-scope-and-caveats)
- [6. Differences between draft -10 and draft -12](#6-differences-between-draft--10-and-draft--12)
- [7. Reproducing these results](#7-reproducing-these-results)
- [8. References](#8-references)
- [Appendix A. Example of a ProofFrog security definition](#appendix-a-example-of-a-prooffrog-security-definition)

---

## 1. Summary

We developed ProofFrog [[EMS25]](#ref-ems25) models of all 4 hybrid KEM frameworks (CG, CK, UG, UK) in the draft's Sections [5.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.3) to [5.6](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.6), for both the seeded and expanded variants. We have a total of 57 machine-checked ProofFrog proofs showing correctness, hybrid IND-CCA security (both traditional and post-quantum branches), and binding properties (LEAK-BIND-K-{CT,PK} and HON-BIND-K-{CT,PK}). The full matrix of results is in [Section 3 of this report](#3-provable-security-analysis).

Our analysis was done on draft version [**-10**](#ref-hybrid-10), whereas the version under last call is [**-12**](#ref-hybrid-12). [Section 2 of this report](#2-draft--10-versus-draft--12) summarizes the differences, and [Section 6](#6-differences-between-draft--10-and-draft--12) gives them in full.

We did not find any attacks, and most of the claims made in the draft are supported by our analysis. For some binding security properties that the draft states as holding in the standard model, we were able to give proofs only in the random oracle model, and we suggest that those claims be clarified.

**Findings**:

  1. **[Finding F1](#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model).** We were unable to show LEAK binding for CG-seeded and CK-seeded in the standard model, and obtained it only in the random oracle model. Draft -12 Section [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2) makes the seed format the primary definition of the decapsulation key, so the format the draft prefers is the one for which our results are weaker. (Draft Sections [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2), [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2), and 6.4.1.)
  2. **[Finding F2](#f2-the-traditional-branches-of-ug-and-cg-depend-on-a-variant-of-sdh-over-shared-secret-encodings-not-group-elements).** The traditional branches of UG and CG depend on a variant of the strong Diffie-Hellman assumption whose target and decision oracle range over shared-secret encodings rather than group elements, and not on the assumption draft -12 Section [6.2.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.2.1) specifies. We are not aware of a reduction establishing that either assumption implies the other. (Draft Sections [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2), [6.1.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.1.3), and 6.2.1.)
  3. **[Finding F3](#f3-the-seed-based-analyses-repeatedly-assume-that-generatekeypair-is-equivalent-to-derivekeypair-on-a-random-seed).** Every seed-based analysis assumes that a component's GenerateKeyPair is equivalent to DeriveKeyPair on a random seed. Draft -12 states this identity for the hybrid constructions in Section [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2), but does not explicitly assume it of the components. (Draft Sections [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1), [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2), [4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.1), and 6.2.)
  4. **[Finding F4](#f4-draft--12-discusses-rejection-handling-but-does-not-apply-it-in-the-pseudocode-or-the-cg-and-ck-binding-arguments).** Draft -12 discusses rejection handling in Sections [4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.1) and [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2), but does not apply it in the decapsulation pseudocode of Sections [5.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.3) to [5.6](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.6), nor in the binding argument for CG and CK. (Draft Sections [4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.1), [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2), [5.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.3) to [5.6](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.6), and 6.4.2.)
  5. **[Finding F5](#f5-indifferentiability-of-the-kdf-is-not-needed-for-most-of-the-results).** Indifferentiability of the KDF is needed only for the traditional branches of UG and CG. Six of the eight IND-CCA results assume only that the KDF is a pseudorandom function, and every binding result assumes only that it is collision resistant. (Draft Sections [6.1.5](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.1.5) and [6.2.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.2.1).)

We support publication once the claims identified in [Finding F1](#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model) are clarified. The changes we suggest are to the security considerations text rather than to the constructions, and are set out in [Section 4 of this report](#4-findings-and-suggested-changes).

**Artifacts.** ProofFrog models referenced in this report can be found in <https://github.com/ProofFrog/examples/tree/main/applications/cfrg-hybrid-kems>. See [Section 7](#7-reproducing-these-results) for instructions on reproducing the results.

**Caveats.** ProofFrog is a new tool with a large trusted code base and does not have the same level of assurance as existing proof verification tools like EasyCrypt [[BGHZ11]](#ref-bghz11), [[BDGKSS14]](#ref-bdgkss14). See [Section 5 of this report](#5-scope-and-caveats) for more discussion of the limitations and caveats.

---

## 2. Draft -10 versus draft -12

Our ProofFrog-based analysis was done on draft version **-10**, whereas the last call version of the draft is **-12**. We compared the two versions to see what aspects of the analysis are affected.

There are three notable differences:

- New text at the end of draft -12 Section [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1) argues the equivalence of the seeded and expanded versions and discusses applicability to the binding property proof sketches; we address this in [Finding F1](#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model) and [Finding F3](#f3-the-seed-based-analyses-repeatedly-assume-that-generatekeypair-is-equivalent-to-derivekeypair-on-a-random-seed).
- A new paragraph in draft -12 Section [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2) classifies some nominal groups as explicitly rejecting KEMs. We did not model explicit rejection, so our binding results do not cover those instantiations; see [Section 5.1 of this report](#51-what-we-did-not-check).
- Section [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2) of draft -12 specifies the expanded decapsulation key format that draft -10 left ambiguous; this conveniently matches the modelling we chose in our draft -10 mechanization.

[Section 6 of this report](#6-differences-between-draft--10-and-draft--12) details differences between draft -12 and draft -10 and how they affect this work.

---

## 3. Provable security analysis

We modelled each of the four hybrid combiner frameworks (CG, CK, UG, UK) in both decapsulation key formats (seeded and expanded), and proved correctness, IND-CCA under each of the two underlying assumptions (traditional and post-quantum), and the [CDM24](#ref-cdm24) binding notions LEAK-BIND-K-CT, LEAK-BIND-K-PK, and their HON-BIND counterparts. This section summarizes the results and provides context on how to interpret our formalization.

### 3.1 How to read a ProofFrog security definition

ProofFrog states a security notion as a pair of games rather than as a single game with a win predicate, and the adversary's advantage is its advantage in distinguishing the two. ProofFrog's approach closely follows that of Rosulek's *Joy of Cryptography* [[Ros26]](#ref-ros26). As this differs in presentation style from the normal literature, we work through one sample definition in [Appendix A](#appendix-a-example-of-a-prooffrog-security-definition).

### 3.2 Summary of results

| | [UG<br>seeded](schemes/UG/UG_seedbased.scheme) | [UG<br>expanded](schemes/UG/UG_expanded.scheme) | [UK<br>seeded](schemes/UK/UK_seedbased.scheme) | [UK<br>expanded](schemes/UK/UK_expanded.scheme) | [CG<br>seeded](schemes/CG/CG_seedbased.scheme) | [CG<br>expanded](schemes/CG/CG_expanded.scheme) | [CK<br>seeded](schemes/CK/CK_seedbased.scheme) | [CK<br>expanded](schemes/CK/CK_expanded.scheme) |
|---|---|---|---|---|---|---|---|---|
| T component | NominalGroup | NominalGroup | KEM | KEM | NominalGroup | NominalGroup | KEM | KEM |
| Combiner | Universal | Universal | Universal | Universal | C2PRI | C2PRI | C2PRI | C2PRI |
| Correctness | [✅](proofs/UG/UG_seedbased_Correctness.proof) | [✅](proofs/UG/UG_expanded_Correctness.proof) | [✅](proofs/UK/UK_seedbased_Correctness.proof) | [✅](proofs/UK/UK_expanded_Correctness.proof) | [✅](proofs/CG/CG_seedbased_Correctness.proof) | [✅](proofs/CG/CG_expanded_Correctness.proof) | [✅](proofs/CK/CK_seedbased_Correctness.proof) | [✅](proofs/CK/CK_expanded_Correctness.proof) |
| IND-CCA (PQ branch) | [✅](proofs/UG/UG_seedbased_INDCCA_PQ.proof) | [✅](proofs/UG/UG_expanded_INDCCA_PQ.proof) | [✅](proofs/UK/UK_seedbased_INDCCA_PQ.proof) | [✅](proofs/UK/UK_expanded_INDCCA_PQ.proof) | [✅](proofs/CG/CG_seedbased_INDCCA_PQ.proof) | [✅](proofs/CG/CG_expanded_INDCCA_PQ.proof) | [✅](proofs/CK/CK_seedbased_INDCCA_PQ.proof) | [✅](proofs/CK/CK_expanded_INDCCA_PQ.proof) |
| IND-CCA (T branch) | [✅](proofs/UG/UG_seedbased_INDCCA_T.proof) (ROM) | [✅](proofs/UG/UG_expanded_INDCCA_T.proof) (ROM) | [✅](proofs/UK/UK_seedbased_INDCCA_T.proof) | [✅](proofs/UK/UK_expanded_INDCCA_T.proof) | [✅](proofs/CG/CG_seedbased_INDCCA_T.proof) (ROM) | [✅](proofs/CG/CG_expanded_INDCCA_T.proof) (ROM) | [✅](proofs/CK/CK_seedbased_INDCCA_T.proof) | [✅](proofs/CK/CK_expanded_INDCCA_T.proof) |
| LEAK-BIND-K-CT (std model) | [✅](proofs/UG/UG_seedbased_LEAK_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/UG/UG_seedbased_LEAK_BIND_K_CT_SAMEKEY.proof) | [✅](proofs/UG/UG_expanded_LEAK_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/UG/UG_expanded_LEAK_BIND_K_CT_SAMEKEY.proof) | [✅](proofs/UK/UK_seedbased_LEAK_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/UK/UK_seedbased_LEAK_BIND_K_CT_SAMEKEY.proof) | [✅](proofs/UK/UK_expanded_LEAK_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/UK/UK_expanded_LEAK_BIND_K_CT_SAMEKEY.proof) | **not proved** | [✅](proofs/CG/CG_expanded_LEAK_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/CG/CG_expanded_LEAK_BIND_K_CT_SAMEKEY.proof) | **not proved** | [✅](proofs/CK/CK_expanded_LEAK_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/CK/CK_expanded_LEAK_BIND_K_CT_SAMEKEY.proof) |
| LEAK-BIND-K-PK (std model) | [✅](proofs/UG/UG_seedbased_LEAK_BIND_K_PK.proof) | [✅](proofs/UG/UG_expanded_LEAK_BIND_K_PK.proof) | [✅](proofs/UK/UK_seedbased_LEAK_BIND_K_PK.proof) | [✅](proofs/UK/UK_expanded_LEAK_BIND_K_PK.proof) | **not proved** | [✅](proofs/CG/CG_expanded_LEAK_BIND_K_PK.proof) | **not proved** | [✅](proofs/CK/CK_expanded_LEAK_BIND_K_PK.proof) |
| LEAK-BIND-K-CT (PRG as RO) | n/a | n/a | n/a | n/a | [✅](proofs/CG/CG_seedbased_LEAK_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/CG/CG_seedbased_LEAK_BIND_K_CT_SAMEKEY.proof) (ROM) | n/a | [✅](proofs/CK/CK_seedbased_LEAK_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/CK/CK_seedbased_LEAK_BIND_K_CT_SAMEKEY.proof) (ROM) | n/a |
| LEAK-BIND-K-PK (PRG as RO) | n/a | n/a | n/a | n/a | [✅](proofs/CG/CG_seedbased_LEAK_BIND_K_PK.proof) (ROM) | n/a | [✅](proofs/CK/CK_seedbased_LEAK_BIND_K_PK.proof) (ROM) | n/a |
| HON-BIND-K-CT (std model) | implied | implied | implied | implied | [✅](proofs/CG/CG_seedbased_HON_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/CG/CG_seedbased_HON_BIND_K_CT_SAMEKEY.proof) | implied | [✅](proofs/CK/CK_seedbased_HON_BIND_K_CT_DIFFKEY.proof) / [✅](proofs/CK/CK_seedbased_HON_BIND_K_CT_SAMEKEY.proof) | implied |
| HON-BIND-K-PK (std model) | implied | implied | implied | implied | [✅](proofs/CG/CG_seedbased_HON_BIND_K_PK.proof) | implied | [✅](proofs/CK/CK_seedbased_HON_BIND_K_PK.proof) | implied |

The cells in the IND-CCA (T branch) row marked *ROM* model the combiner KDF as a random oracle, and the two rows labelled *PRG as RO* model the seed-expansion PRG as one; every other cell is a standard-model result. The UG and CG cells in the IND-CCA (T branch) row additionally rest on a variant of the strong Diffie-Hellman assumption rather than the one the draft specifies; see [Finding F2](#f2-the-traditional-branches-of-ug-and-cg-depend-on-a-variant-of-sdh-over-shared-secret-encodings-not-group-elements). The **not proved** cells are discussed in [Finding F1](#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model).

### 3.3 Modelling choices

**Splitting the X-BIND-K-CT game.** The X-BIND-K-CT game of [CDM24](#ref-cdm24) gives the adversary a bit to select between two ways of winning: either finding a collision across two independently generated receiver key pairs, or a second ciphertext that decapsulates to the same shared secret under a single key. A KEM satisfies the notion if and only if it withstands both. To simplify the mechanized proofs, we model the two as separate games — `LEAK_BIND_K_CT_DIFFKEY` and `LEAK_BIND_K_CT_SAMEKEY` — and prove both. The preamble that draft -12 added to Section [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2) makes the same case distinction.

**The two key formats.** Draft -12 Section [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2) defines the decapsulation key to be a seed, from which decapsulation re-derives both component key pairs on every call, and permits an expanded format `(dk_PQ, ek_PQ, dk_T, ek_T)` for deployments that cannot implement the seed format. We model both. Our security properties are all phrased in terms of the expanded form that is more commonly seen in the literature. Thus, every seed-form proof begins by bridging to the expanded form: PRG security replaces the seed with two independent uniform component seeds, and [`KeyGenEquiv`](games/KEM/KeyGenEquiv.game), applied once per component KEM, replaces `DeriveKeyPair` on a uniform seed with the component's own key generation, which is the form in which the component assumptions are stated.

This bridge between seeded and expanded form is available exactly when the seed is hidden from the adversary. In the correctness, IND-CCA and HON-BIND games it is, so both formats admit the same proof. However, in the LEAK-BIND games the adversary is given the decapsulation key, which in the seed format is the seed, so PRG security cannot be invoked. That is the difficulty behind [Finding F1](#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model), and the second step of the bridge is discussed in [Finding F3](#f3-the-seed-based-analyses-repeatedly-assume-that-generatekeypair-is-equivalent-to-derivekeypair-on-a-random-seed).

### 3.4 Assumptions and theorem bounds

Each ProofFrog proof file includes the list of assumptions used in the theorem and the accumulated advantage bound.

The assumptions fall into three kinds. Most are cryptographic hardness assumptions on underlying building blocks, which therefore contribute a corresponding advantage term; one of them, for the traditional branches of UG and CG, is not the assumption the draft specifies, as discussed in [Finding F2](#f2-the-traditional-branches-of-ug-and-cg-depend-on-a-variant-of-sdh-over-shared-secret-encodings-not-group-elements). A few are statistical facts about reprogramming a random oracle, whose distinguishing advantage can be calculated statistically, and for which we have LLM-written EasyCrypt proofs. And one assumption, the equivalence between a component's key generation and derivation from a uniform seed, we treat as definitional; see [Finding F3](#f3-the-seed-based-analyses-repeatedly-assume-that-generatekeypair-is-equivalent-to-derivekeypair-on-a-random-seed).

The full list of assumptions and advantage bounds are in [BOUNDS-CFRG-20260722.md](BOUNDS-CFRG-20260722.md). Here we summarize a few notable observations. Every binding result for the universal combiners reduces to collision resistance of the KDF alone. Binding results for the C2PRI combiners additionally depend on the corresponding binding notion on the post-quantum component. No binding result requires indifferentiability of the KDF, and none requires C2PRI; on where indifferentiability is and is not needed, see [Finding F5](#f5-indifferentiability-of-the-kdf-is-not-needed-for-most-of-the-results).

### 3.5 Exporting from ProofFrog to EasyCrypt

ProofFrog has a work-in-progress exporter that converts a ProofFrog proof to an EasyCrypt proof, so that a second and more mature proof assistant can be used to check the argument. (These can be found on the `easycrypt` branches of the ProofFrog [engine](https://github.com/ProofFrog/ProofFrog/tree/easycrypt) and [examples](https://github.com/ProofFrog/examples/tree/easycrypt) repositories.)

As of July 22, 2026, 28 of the 57 proofs are accepted in EasyCrypt.

| Result class | Accepted admit-free in EasyCrypt |
|---|---|
| Correctness | 8 / 8 |
| Binding (LEAK / HON) | 17 / 30 |
| Generic LEAK => HON lemmas | 3 / 3 |
| IND-CCA | 0 / 16 |

Of the six CG-seeded and CK-seeded LEAK-BIND proofs, which are the results that rest on modelling the seed-expansion PRG as a random oracle, only `CG_seedbased_LEAK_BIND_K_CT_SAMEKEY` is currently exported and accepted. The DIFFKEY and K-PK proofs for both schemes, and the CK-seeded SAMEKEY proof, are not yet accepted, nor are any of the seeded HON-BIND proofs.

For the results that are not yet exporting accepted proofs to EasyCrypt, it is because the exporter is an unfinished work in progress, not because we know of any barrier to proving them in EasyCrypt.
 
An important caveat is that **the exported EasyCrypt versions have not been reviewed by an EasyCrypt expert.** An admit-free `ec_compile` establishes that EasyCrypt accepts the proof *as written*. It does not establish that what was written faithfully models the intended statement: the module and adversary-class declarations, the memory-restriction annotations, the declared axioms, and the distribution assumptions are all ours, and an error in any of them would produce a proof that compiles cleanly while proving something other than what we claim or what we intend to claim. The same caution applies to the LLM-written helper proofs listed in [the assumption ledger in BOUNDS-CFRG-20260722.md](BOUNDS-CFRG-20260722.md#2-the-assumptions). We would welcome review by someone fluent in EasyCrypt's semantics.

The places we would most want a reviewer to look are: the memory restrictions on the adversary classes, which if stated too loosely make a lemma weaker than it appears and if stated too tightly make it inapplicable where we use it; the axioms declared in the LLM-written helper proofs, listed in [the assumption ledger in BOUNDS-CFRG-20260722.md](BOUNDS-CFRG-20260722.md#2-the-assumptions); and whether an exported module faithfully mirrors the ProofFrog game it was generated from, which is a question about our exporter rather than about EasyCrypt.

---

## 4. Findings and suggested changes

### F1. LEAK binding for CG-seeded and CK-seeded is not established in the standard model

**Relevant draft sections.** Draft -12 Sections [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2), [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2), and [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1) (final paragraph).

Every [LEAK-BIND](games/KEM/Binding/) result in our suite holds in the standard model except for CG-seeded and CK-seeded. For these, we were only able to show LEAK-BIND-K-CT and LEAK-BIND-K-PK by modelling the seed-expansion PRG as a programmable random oracle. We were able to show LEAK binding in the standard model for UG and UK in either key format, and for CG-expanded and CK-expanded. We were also able to show that CG-seeded and CK-seeded satisfy HON-BIND in the standard model.

The reason we encountered this difficulty is as follows. In the LEAK-BIND games of [CDM24](#ref-cdm24), the adversary is given the honestly generated decapsulation key, which in the seed format is the seed itself. For UG and UK, the binding argument reduces a collision on distinct ciphertexts or public keys directly to a KDF collision. Notably, it does not reduce to a binding property of the underlying KEM; thus the seed plays no role and both key formats admit the same proof. The difficulty arises only when the argument must relate the hybrid seed to a component decapsulation key while the adversary holds that seed. In the HON-BIND games the adversary is not given the decapsulation key, which is why those results go through.

We emphasize that we did not find an attack, and we do not claim that seed-format binding fails for CG or CK. We have also not shown that no standard-model proof exists, and whether some less direct argument succeeds is open.

Draft -12 Section [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2) makes the seed format the primary definition of the decapsulation key, and permits the expanded format only for deployments that cannot implement it. Our standard-model binding results for CG and CK are for the expanded format, so the format the draft prefers is the one for which our results are weaker.

The closing paragraph of draft -12 Section [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1) concludes that "the same observation underlies the binding sketches in Section [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2)", extending to binding an argument it makes for IND-CCA. For CG-seeded and CK-seeded, that is the step we were unable to take.

**Suggested change.** Replace the final sentence of the closing paragraph of Section [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1):

```
- The same observation underlies the binding sketches in Section 6.4.2.

+ This argument applies to the IND-CCA analyses above, in which the seed is
+ not available to the adversary. It does not apply to the LEAK-BIND analyses
+ of Section 6.4.2, in which the adversary is given the decapsulation key:
+ when the decapsulation key is the shared seed, the adversary can recompute
+ the PRG output, and PRG security cannot be invoked.
```

The binding sketches for CG and CK would then need to be stated as random-oracle-model results for the seed format, or scoped to the expanded format. We also suggest recording in Section [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2) that the two key formats do not carry equivalent binding guarantees.

---

### F2. The traditional branches of UG and CG depend on a variant of SDH over shared-secret encodings, not group elements

**Relevant draft sections.** Draft -12 Sections [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2), [6.1.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.1.3), and 6.2.1.

Draft -12 Section [6.2.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.2.1) requires, for the traditional branch of the group-based frameworks, that the strong Diffie-Hellman problem be hard in Group_T. Our UG and CG traditional-branch IND-CCA proofs do not reduce to that assumption. They reduce to a variant, which we call [`SDH_SS`](games/Group/SDH_SS.game), in which the adversary must produce the shared-secret encoding of the Diffie-Hellman element, as computed by ElementToSharedSecret, rather than the element itself, and in which the decision oracle likewise ranges over shared-secret encodings rather than over group elements.

The two assumptions therefore differ in what the adversary must produce and in what the decision oracle answers about. Draft -12 Section [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2) does not require ElementToSharedSecret to be injective, and gives the X-coordinate map as its example, which is two-to-one. A shared-secret encoding need not determine the group element it encodes, so neither the adversary's output nor the decision oracle carries over between the two settings in any direct way. We are not aware of a reduction establishing that either assumption implies the other.

Our [nominal group primitive](primitives/NominalGroup.primitive) deliberately omits the injectivity modifier, faithful to draft -12 Section [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2). Had we declared the map injective, the engine would treat its output as determining its input, and the distinction would not have arisen. For the X-coordinate instantiation that the draft itself mentions, the difference is therefore not an artifact of how we chose to state the assumption.

**Suggested change.** We suggest that Sections [6.1.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.1.3) and [6.2.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.2.1) refer to the variant over shared-secret encodings explicitly.

---

### F3. The seed-based analyses repeatedly assume that GenerateKeyPair is equivalent to DeriveKeyPair on a random seed

**Relevant draft sections.** Draft -12 Sections [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1) (final paragraph), [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2), [4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.1), and 6.2.

The closing paragraph of draft -12 Section [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1), discussed in [Finding F1](#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model), relies on a second hypothesis that it does not state. PRG security carries the argument from the shared seed to two independent uniform seeds; getting from there to the independently generated key pairs that the published analyses model requires, for each component, that DeriveKeyPair applied to a uniform seed induce the same key pair distribution as GenerateKeyPair. This applies wherever the argument is used, including the IND-CCA analyses.

Draft -12 states this identity of the hybrid, in Section [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2), but not of the components: Section [4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.1) lists GenerateKeyPair and DeriveKeyPair as two algorithms of a KEM without asserting any relationship between them. It holds by definition for the KEMs the draft targets, ML-KEM among them, but does not necessarily hold in general, since a KEM whose seed is substantially shorter than the randomness its GenerateKeyPair consumes satisfies Section [4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.1) while DeriveKeyPair on a uniform seed would output only a sparse set of key pairs. In our mechanization, this is captured via the [`KeyGenEquiv`](games/KEM/KeyGenEquiv.game) game, invoked once per component KEM in every seed-form proof.

**Suggested change.** The requirement would sit naturally alongside the other component requirements in Section [6.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.2). Failing that, append to the closing paragraph of Section [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1):

```
+ This argument also assumes that, for each component, DeriveKeyPair applied
+ to a uniform seed induces the same key pair distribution as
+ GenerateKeyPair. This holds by definition for components whose
+ GenerateKeyPair is specified as DeriveKeyPair applied to fresh randomness,
+ including ML-KEM, but it does not follow from the algorithm interface of
+ Section 4.1 alone.
```

---

### F4. Draft -12 discusses rejection handling but does not apply it in the pseudocode or the CG and CK binding arguments

**Relevant draft sections.** Draft -12 Sections [4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.1), [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2), [5.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.3) to [5.6](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.6), and 6.4.2.

Draft -12 makes rejection explicit: Section [4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.1) states that decapsulation may return an error, and Section [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2) states that the hybrid returns an error when Group_T.Exp does. Two places in the draft do not reflect that addition.

The first is the pseudocode. Decapsulation in Sections [5.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.3) to [5.6](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.6) computes a shared secret unconditionally in all four frameworks, with no check that the component decapsulations succeeded. Three of the four previous provable security analyses the draft cites include such a check and return a rejection symbol if either component fails: [StarFortress](#ref-cg26) for UG, [X-Wing](#ref-xwing) for CG, and [GHP18](#ref-ghp18) for UK. The fourth, [StarHunters](#ref-cos26) for CK, does not.

The second is the binding argument. The preamble to Section [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2) argues that the collision arguments are unaffected by how rejection is signalled, because the binding games are won only by a collision on non-rejecting keys, so both decapsulations must succeed. For UG and UK that argument terminates in a KDF collision and is easy to follow. For CG and CK it does not terminate there: it continues into a reduction to binding of the post-quantum component, which is where rejection behaviour could matter. We did not (yet) model explicit rejection, so we cannot offer a conclusion at this point; see [Section 5.1 of this report](#51-what-we-did-not-check).

**Suggested change.** We suggest separately stating explicit-rejection versions of the decapsulation pseudocode in Sections [5.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.3) to [5.6](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.6). We also suggest that the rejection-aware argument in the preamble to Section [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2) be given explicitly for CG and CK.

---

### F5. Indifferentiability of the KDF is not needed for most of the results

**Relevant draft sections.** Draft -12 Sections [6.1.5](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.1.5) and 6.2.1.

Draft -12 Section [6.1.5](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.1.5) requires that the KDF be indifferentiable from a random oracle, even to a quantum attacker. Section [6.2.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.2.1) observes that some IND-CCA analyses require only a PRF-style assumption instead, and says that for simplicity the draft ignores this. Our results make that alternative concrete.

Six of the eight IND-CCA results are standard-model results assuming only that the KDF is a pseudorandom function: the post-quantum branches of all four frameworks key it on the post-quantum shared secret, as [`KDFPRFSec`](games/KDF/KDFPRFSec.game) for UG and CG and the split-key [`KDFFirstKeyPRF`](games/KDF/KDFFirstKeyPRF.game) for UK and CK, and the traditional branches of UK and CK key it on the traditional shared secret, as [`KDFSecondKeyPRF`](games/KDF/KDFSecondKeyPRF.game). The exceptions are the traditional branches of UG and CG, which model the KDF as a random oracle. Every binding result assumes only collision resistance, as [`KDFCollisionResistance`](games/KDF/KDFCollisionResistance.game).

**Suggested change.** Indifferentiability from a random oracle, and against quantum adversaries in particular, is a strong requirement to place on an implementation. We suggest that Section [6.2.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.2.1) replace the observation that the alternative is ignored for simplicity with a statement of which assumptions suffice for which results, and that Section [6.1.5](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.1.5) record that indifferentiability is required only where a proof models the KDF as a random oracle.

---

## 5. Scope and caveats

### 5.1 What we did not check

Let us highlight several things this analysis does not address.

**Concrete instantiations.** Every proof is generic over the component KEM and the nominal group. We do not prove anything about ML-KEM, X25519, P-256 or any other concrete choice, beyond what follows from assuming the properties listed in [the assumption ledger in BOUNDS-CFRG-20260722.md](BOUNDS-CFRG-20260722.md#2-the-assumptions).

**Quantum adversaries.** ProofFrog implicitly models adversaries as classical. As with general provable security results, a standard-model result carries over to quantum adversaries provided every assumption it rests on holds against them. A random-oracle-model result does not carry over, since a classical-random-oracle reduction can fail against an adversary that queries in superposition.

**MAL-BIND.** Draft -12 Section [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2) comments that shared-seed key generation can contribute to binding against an adversary that chooses the keys, and says it does not prove this. We do not prove it either. All binding results in this analysis are either LEAK or HON results.

**Expert review of the exported EasyCrypt models and proofs.** See [Section 3.5](#35-exporting-from-prooffrog-to-easycrypt).

**Byte-level encodings.** We have abstracted the formatting and layout of the seed and label: the encoding functions are declared with the injectivity and determinism our proofs require, but their layouts are not given. We are therefore assuming that a concrete instantiation achieves the injectivity we declare, and a layout that did not would invalidate the results depending on it.

**Explicit rejection.** Our [KEM primitive](primitives/KEM.primitive) declares decapsulation as a total function: it returns a shared secret, and there is no distinguished rejection symbol. Our [binding games](games/KEM/Binding/) therefore do not check for rejection in the win condition. The hybrid ciphertext type compounds this, since it restricts the traditional-side ciphertext to valid group elements, so a decoding failure is not expressible in our model at all. These choices are sound for implicitly rejecting KEMs, such as ML-KEM.

Draft -12 Section [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2) states that for some groups, P-256 and ristretto255 among them, there exist byte strings of the correct length that do not decode to a group element; that Exp returns an error on such an input; and that a hybrid KEM whose nominal group can fail in this way is an instance of an explicitly rejecting KEM. Hence our binding results for CG and UG do not cover those instantiations. Our results only apply to groups in which every byte string of the appropriate length decodes to an element, such as X25519.

Draft -12 Section [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2) argues that the collision arguments are unaffected by how rejection is signalled, on the grounds that the binding games are won only by a collision on non-rejecting keys, so both decapsulations must succeed. That argument appears sound to us for the cases which terminate in a KDF collision, but we did not mechanize it, and we neither confirm nor refute it. Extending the model to explicit rejection, and checking that argument for CG and CK, is future work; see [Finding F4](#f4-draft--12-discusses-rejection-handling-but-does-not-apply-it-in-the-pseudocode-or-the-cg-and-ck-binding-arguments).

### 5.2 Limitations of ProofFrog

ProofFrog [[EMS25]](#ref-ems25) is a research prototype rather than a verified proof assistant. It verifies a game-hopping proof by canonicalizing the abstract syntax of the two games at each hop and discharging the remaining side conditions to Z3 and SymPy. Both the canonicalization pipeline and the semantics of FrogLang that it implicitly assumes are under active development.

A proof that verifies is therefore *some* mechanically checked evidence that the claimed hops are sound under the engine's interpretation of FrogLang. It is not a fully formalized proof comparable to one in Rocq, Lean, or EasyCrypt. 

Using ProofFrog's work-in-progress EasyCrypt exporter, we have checked some proofs in EasyCrypt. While EasyCrypt itself is mature, our EasyCrypt exporter is not. As set out in [Section 3.5](#35-exporting-from-prooffrog-to-easycrypt), an EasyCrypt proof can be accepted, but if the modelling or assumptions used are problematic, the result may not be meaningful.

At this point, we hope that the reader views the ProofFrog results in this work as suggestive, but not definitive. We do note that ProofFrog's proof files themselves are human readable; they include the reductions claimed to justify each game hop, and in principle a reader could evaluate them at the same level as in a standard pen-and-paper proof.

### 5.3 Use of AI assistance

We used an LLM coding agent (Claude) throughout this work: in authoring the ProofFrog models, the proof scripts, the intermediate games and the reductions; in the EasyCrypt export, including the EasyCrypt proofs of the statistical helper bounds, which the agent wrote directly rather than generating them from ProofFrog; and in drafting this report. Substantial parts of the ProofFrog engine itself were also written primarily by AI coding agents, so the checker is partly agent-authored as well as the proofs it checks.

We as authors reviewed the ProofFrog models of every primitive, scheme, and security definition, and evaluated the assumptions used in each proof. We provided input guiding the LLM coding agent in developing proofs, including providing simpler prototype proofs, and suggesting proof directions. We were heavily involved in the standard model / random oracle model issues of the LEAK-BIND proofs for the seeded variants.

---

## 6. Differences between draft -10 and draft -12

This section expands on [Section 2](#2-draft--10-versus-draft--12) and details differences between draft -10 (the version our models were built against) and the version under last call (-12).

| Draft -12 section | Change from -10 to -12 | Effect on this work |
|---|---|---|
| [4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.1) | `Decaps` MAY now return an error; the interface covers both implicitly and explicitly rejecting KEMs, and "the security analyses in Section [6](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6) take this variation into account" | The draft now makes an explicit claim about rejection handling that our models do not express; see [Section 5.1](#51-what-we-did-not-check) and [Finding F4](#f4-draft--12-discusses-rejection-handling-but-does-not-apply-it-in-the-pseudocode-or-the-cg-and-ck-binding-arguments). |
| [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2) | New paragraph classifying nominal groups with non-decoding byte strings (P-256, ristretto255) as **explicitly rejecting** KEMs; `Group_T.Exp` returns an error, so hybrid `Decaps` returns an error | Our binding results assume implicit rejection, so they do not cover UG or CG over these groups; see [Section 5.1](#51-what-we-did-not-check). |
| [4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-4.2) | Nominal group: scalars are integers mod `r`; zero scalar MUST NOT be used as a private key | No effect; our `RandomScalar` is abstract. |
| [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2) | Expanded key form now **fully specified**: `dk_H = (dk_PQ, ek_PQ, dk_T, ek_T)`, `ek_H = (ek_PQ, ek_T)`, and `expandDecapsKey` simply destructures | Resolves an ambiguity we had flagged in our -10 models. Our `*_expanded.scheme` files match the -12 text. Our expanded-form results now correspond to a form the draft specifies rather than one we constructed. |
| [5.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-5.2) | New `DecapsToEncaps(dk)` subroutine | No effect on our models. |
| [6.1.5](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.1.5) | HKDF indifferentiability condition rewritten: domain-disjointness per [LBB20] Lemma 6, replacing the prefix-collision condition | No effect; we assume PRF-style properties of the KDF, not indifferentiability (see [Finding F5](#f5-indifferentiability-of-the-kdf-is-not-needed-for-most-of-the-results)). |
| [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1) | New closing paragraph: component key pairs derived from one seed are indistinguishable from independent key pairs by PRG security, therefore the independent-keys IND-CCA analyses transfer; **"The same observation underlies the binding sketches in Section [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2)."** | **Relates to Findings [F1](#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model) and [F3](#f3-the-seed-based-analyses-repeatedly-assume-that-generatekeypair-is-equivalent-to-derivekeypair-on-a-random-seed).** The argument is correct for IND-CCA and HON-BIND, but it does not go through for LEAK-BIND, which is where our seed-format gap lies ([Finding F1](#f1-leak-binding-for-cg-seeded-and-ck-seeded-is-not-established-in-the-standard-model)); it also silently requires a component-level `DeriveKeyPair` / `GenerateKeyPair` identity ([Finding F3](#f3-the-seed-based-analyses-repeatedly-assume-that-generatekeypair-is-equivalent-to-derivekeypair-on-a-random-seed)). |
| [6.4.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.1) | Attribution corrected: `[COS_26]` describes the analysis of **CK** (was "UG"); `[CG26]` ([StarFortress](#ref-cg26)) added for UG | Corrects the attribution of the CK and UG analyses; no effect on our models. |
| [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2) | New preamble to the binding sketches: LEAK-BIND is described with two honestly-generated key pairs, the adversary may set the second equal to the first, "so the analyses also cover the case of a single key pair" | This is the DIFFKEY/SAMEKEY split we mechanized ([Section 3.3 of this report](#33-modelling-choices)); we prove both cases separately. |
| [6.4.2](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.4.2) | New preamble: `reject` replaces `bot`; LEAK-BIND is won only on non-reject keys, "so the collision arguments below ... are unaffected by how rejection is signaled" | We did not model explicit rejection and neither confirm nor refute it; see [Section 5.1](#51-what-we-did-not-check) and [Finding F4](#f4-draft--12-discusses-rejection-handling-but-does-not-apply-it-in-the-pseudocode-or-the-cg-and-ck-binding-arguments). |
| [6.5.1](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hybrid-kems-12#section-6.5.1) | Label domain separation corrected from **prefix-free** to **suffix-free** | No effect; labels are abstracted in our models. |

---

## 7. Reproducing these results

The ProofFrog models, the proof scripts, and the generated bound tables are at <https://github.com/ProofFrog/examples/tree/main/applications/cfrg-hybrid-kems>. The results reported here are those of commit `a2e66f7`.

[`README.md`](README.md) in that directory gives the commands to parse and type-check the primitives, games and schemes, and to verify every proof. Verifying a single proof also prints its hop sequence and the advantage bound it establishes.

---

## 8. References

- <a id="ref-bdgkss14"></a>**[BDGKSS14]** Gilles Barthe, François Dupressoir, Benjamin Grégoire, César Kunz, Benedikt Schmidt, Pierre-Yves Strub. *EasyCrypt: A Tutorial.* Foundations of Security Analysis and Design VII, LNCS 8604, 2014, pp. 146-166. <https://doi.org/10.1007/978-3-319-10082-1_6>
- <a id="ref-bghz11"></a>**[BGHZ11]** Gilles Barthe, Benjamin Grégoire, Sylvain Heraud, Santiago Zanella Béguelin. *Computer-Aided Security Proofs for the Working Cryptographer.* CRYPTO 2011, LNCS 6841, pp. 71-90. <https://doi.org/10.1007/978-3-642-22792-9_5>
- <a id="ref-cdm24"></a>**[CDM24]** Cas Cremers, Alexander Dax, Niklas Medinger. *Keeping Up with the KEMs: Stronger Security Notions for KEMs and Automated Analysis of KEM-based Protocols.* ACM CCS 2024. <https://eprint.iacr.org/2023/1933>
- <a id="ref-cg26"></a>**[CG26]** Deirdre Connolly, Paul Grubbs. *StarFortress: Hybrid KEMs with Diffie-Hellman Inlining.* IACR Communications in Cryptology 3(1), 2026. <https://doi.org/10.62056/ahmp-49p1>
- <a id="ref-cos26"></a>**[COS26]** Deirdre Connolly, Mike Ounsworth, Sophie Schmieg, Douglas Stebila. *StarHunters: Secure Hybrid Post-Quantum KEMs From IND-CCA2 PKEs.* 2026. <https://eprint.iacr.org/2026/427>
- <a id="ref-ems25"></a>**[EMS25]** Ross Evans, Matthew McKague, Douglas Stebila. *ProofFrog: A Tool For Verifying Game-Hopping Proofs.* 2025. <https://eprint.iacr.org/2025/418>
- <a id="ref-ghp18"></a>**[GHP18]** Federico Giacon, Felix Heuer, Bertram Poettering. *KEM Combiners.* PKC 2018. <https://eprint.iacr.org/2018/024>
- <a id="ref-hybrid-10"></a>**[HYBRID-10]** Deirdre Connolly, Richard Barnes, Paul Grubbs. *Hybrid PQ/T Key Encapsulation Mechanisms.* Internet-Draft draft-irtf-cfrg-hybrid-kems-10, 2 March 2026. <https://datatracker.ietf.org/doc/draft-irtf-cfrg-hybrid-kems/10/>
- <a id="ref-hybrid-12"></a>**[HYBRID-12]** Deirdre Connolly, Richard Barnes, Paul Grubbs. *Hybrid PQ/T Key Encapsulation Mechanisms.* Internet-Draft draft-irtf-cfrg-hybrid-kems-12, 6 July 2026. <https://datatracker.ietf.org/doc/draft-irtf-cfrg-hybrid-kems/12/>
- <a id="ref-ros26"></a>**[Ros26]** Mike Rosulek. *The Joy of Cryptography.* MIT Press, 2026. Online edition at <https://joyofcryptography.com>
- <a id="ref-xwing"></a>**[XWING]** Manuel Barbosa, Deirdre Connolly, João Diogo Duarte, Aaron Kaiser, Peter Schwabe, Karolin Varner, Bas Westerbaan. *X-Wing: The Hybrid KEM You've Been Looking For.* IACR Communications in Cryptology 1(1), 2024. <https://doi.org/10.62056/a3qj89n4e>

---

## Appendix A. Example of a ProofFrog security definition

The example below is [`LEAK_BIND_K_PK.game`](games/KEM/Binding/LEAK_BIND_K_PK.game), our ProofFrog formulation of LEAK-BIND-K-PK, the X = LEAK case of the [CDM24](#ref-cdm24) notion X-BIND-K-PK. The file's explanatory header comment is elided here.

```
Game Breakable(KEM K) {
    K.EncapsKey ek0;
    K.EncapsKey ek1;
    K.DecapsKey dk0;
    K.DecapsKey dk1;

    [K.EncapsKey, K.DecapsKey, K.EncapsKey, K.DecapsKey] Initialize() {
        [K.EncapsKey, K.DecapsKey] [ek0, dk0] = K.KeyGen();
        [K.EncapsKey, K.DecapsKey] [ek1, dk1] = K.KeyGen();
        return [ek0, dk0, ek1, dk1];
    }

    Bool Challenge(K.Ciphertext ct0, K.Ciphertext ct1) {
        K.SharedSecret ss0 = K.Decaps(dk0, ct0);
        K.SharedSecret ss1 = K.Decaps(dk1, ct1);
        return ss0 == ss1 && ek0 != ek1;
    }
}

Game Unbreakable(KEM K) {
    K.EncapsKey ek0;
    K.EncapsKey ek1;
    K.DecapsKey dk0;
    K.DecapsKey dk1;

    [K.EncapsKey, K.DecapsKey, K.EncapsKey, K.DecapsKey] Initialize() {
        [K.EncapsKey, K.DecapsKey] [ek0, dk0] = K.KeyGen();
        [K.EncapsKey, K.DecapsKey] [ek1, dk1] = K.KeyGen();
        return [ek0, dk0, ek1, dk1];
    }

    Bool Challenge(K.Ciphertext ct0, K.Ciphertext ct1) {
        K.SharedSecret ss0 = K.Decaps(dk0, ct0);
        K.SharedSecret ss1 = K.Decaps(dk1, ct1);
        return false;
    }
}

export as LEAK_BIND_K_PK;
```

The game is parameterized by the primitive the notion is about: KEM `K`. A proof correspondingly instantiates it with a scheme to be analyzed, such as one of the hybrid combiners. The semantics are that `Initialize` is run once, and what it returns is given to the adversary as input. In this experiment, `Initialize` returns two honestly generated key pairs, both the decapsulation keys and encapsulation keys: that is the "LEAK" in LEAK-BIND.

`Challenge` is an oracle available to the adversary. Since the adversary's goal is to make the two games behave differently, the win condition lives in the difference between the two `Challenge` bodies: `Breakable.Challenge` returns true when two ciphertexts decapsulate to the same shared secret under distinct encapsulation keys, and `Unbreakable.Challenge` never returns true. The distinguishing advantage for the security property is thus the difference between the probabilities that the adversary outputs 1 in the two games. Note that `Unbreakable.Challenge` still computes `ss0` and `ss1` before discarding them. This is a stylistic choice rather than a requirement, since the engine canonicalizes the unused computation away; writing the two games in parallel makes the difference between them easy for a reader to see.

This definition also shows the consequence of our decision to model only implicitly rejecting KEMs. The [CDM24](#ref-cdm24) definition captures explicit rejection by guarding the win condition on both underlying decapsulations succeeding, and no such guard appears here, because our `K.Decaps` is modelled as always returning a `K.SharedSecret` rather than an option type, so there is no rejection symbol to test against. See the discussion in [Section 5.1 of this report](#51-what-we-did-not-check).
