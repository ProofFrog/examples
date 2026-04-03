# KEM Combiner (GHP18)

This directory contains a ProofFrog formalization of the KEM combiner from:

> Federico Giacon, Felix Heuer, and Bertram Poettering.
> "KEM Combiners."
> PKC 2018.
> https://eprint.iacr.org/2018/024

## Construction

The **KEMCombiner** ([KEMCombiner.scheme](KEMCombiner.scheme)) combines two KEMs using a two-key PRF ([TwoKeyPRF.primitive](TwoKeyPRF.primitive)).
Given component KEMs `KEM1` and `KEM2` and a two-key PRF `F`:

- **KeyGen**: Generate key pairs `(pk1, sk1)` and `(pk2, sk2)` independently.
- **Encaps(pk)**: Encapsulate with both KEMs to get `(ss1, ct1)` and `(ss2, ct2)`, then compute the combined shared secret as `ss = F(ss1, ss2, pk1 || ct1 || pk2 || ct2)`.
- **Decaps(sk, ct)**: Decapsulate with both KEMs and recompute the same PRF call.

The label `pk1 || ct1 || pk2 || ct2` binds the public keys and ciphertexts into the PRF evaluation, which is important for achieving CCA-level robustness.

## TwoKeyPRF assumptions

The two-key PRF has single-key and multi-key security notions for each key position:

| Game | Description |
|------|-------------|
| [TwoKeyPRFFirstKeySecurity.game](TwoKeyPRFFirstKeySecurity.game) | Single-key PRF security in the first key (key1 fixed across queries) |
| [TwoKeyPRFSecondKeySecurity.game](TwoKeyPRFSecondKeySecurity.game) | Single-key PRF security in the second key (key2 fixed across queries) |
| [TwoKeyPRFFirstKeyMultiKey.game](TwoKeyPRFFirstKeyMultiKey.game) | Multi-key PRF security in the first key (fresh key1 per query) |
| [TwoKeyPRFSecondKeyMultiKey.game](TwoKeyPRFSecondKeyMultiKey.game) | Multi-key PRF security in the second key (fresh key2 per query) |

The multi-key security properties are derived from the single-key ones via a standard hybrid argument:

- [TwoKeyPRFFirstKeyMultiKeyFromSecurity.proof](TwoKeyPRFFirstKeyMultiKeyFromSecurity.proof): Multi-key first-key security from single-key first-key security (induction over `q` queries).
- [TwoKeyPRFSecondKeyMultiKeyFromSecurity.proof](TwoKeyPRFSecondKeyMultiKeyFromSecurity.proof): Multi-key second-key security from single-key second-key security (induction over `q` queries).

## Correctness proof

[KEMCombinerCorrectness.proof](KEMCombinerCorrectness.proof) shows that the combiner is correct (decapsulation recovers the encapsulated shared secret) assuming both component KEMs are correct:

- Assumptions: `KEMCorrectness(KEM1)`, `KEMCorrectness(KEM2)`
- 5 game hops, reducing to the correctness of each component KEM. The engine's deterministic expression deduplication automatically handles the PRF determinism.

## IND-CPA security proofs

There are two independent proofs that the combiner is IND-CPA-secure, each relying on a different component KEM being secure.
This means the combiner is secure as long as **at least one** of the two component KEMs is secure.

**Proof 1** ([KEMCombinerINDCPA1.proof](KEMCombinerINDCPA1.proof)):
- Assumptions: `CPAKEM(KEM1)` + `TwoKeyPRFFirstKeyMultiKey(F)`
- 7 game hops: replace `KEM1`'s shared secret with random (via IND-CPA assumption), then replace the PRF output with random (via multi-key first-key PRF security).

**Proof 2** ([KEMCombinerINDCPA2.proof](KEMCombinerINDCPA2.proof)):
- Assumptions: `CPAKEM(KEM2)` + `TwoKeyPRFSecondKeyMultiKey(F)`
- 7 game hops: replace `KEM2`'s shared secret with random (via IND-CPA assumption), then replace the PRF output with random (via multi-key second-key PRF security).
