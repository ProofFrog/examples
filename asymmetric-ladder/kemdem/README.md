# KEM-DEM Tutorial (Asymmetric Ladder)

These files are a modernized copy of the KEM-DEM source used in the
[asymmetric-ladder](https://github.com/cryspen/asymmetric-ladder) repository's
ProofFrog KEM-DEM tutorial. They use a deliberately simplified `SymEnc`
primitive (no `KeyGen`, non-nullable `Dec`) so that a KEM-DEM CPA proof can
proceed with a minimal number of reduction hops — three reductions rather
than the five used by the parallel in-repo proof at
`examples/Proofs/PubEnc/KEMDEMCPA.proof`.

The syntax has been updated from the original `A * B` tuple-type form to the
current `[A, B]` form. The pedagogical structure — and its Joy-of-Cryptography
narrative — is preserved. The accompanying manual walkthrough is at
`www/manual/worked-examples/kemdem-cpa.md`.

## Files

- `SymEnc.primitive` — Simplified symmetric encryption (no `KeyGen`).
- `KEM.primitive` — Key encapsulation mechanism interface.
- `PKE.primitive` — Public-key encryption interface.
- `SymEnc-OTS.game` — One-time secrecy for symmetric encryption.
- `KEM-CPA.game` — IND-CPA security for the KEM.
- `PKE-CPA.game` — IND-CPA security for public-key encryption.
- `Hyb.scheme` — The KEM-DEM hybrid construction.
- `Hyb-is-CPA.proof` — Main theorem: `Hyb` is CPA-secure.
