This folder contains proof of security properties for Hybrid Public Key Encryption (HPKE) RFC 9180.

For simplicity and to accommodate Proof Frog's grammar, the following changes have been made:
- Serializing and deserializing public keys are omitted
- Unused optional parameters are omitted
- LabeledExtract and LabeledExpand are omitted
- Concatenation is replaced with tuples
- Byte strings are replaced with bitstrings

References
https://www.rfc-editor.org/rfc/rfc9180.html
https://eprint.iacr.org/2020/1499.pdf