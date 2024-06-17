This folder contains proof of security properties for Hybrid Public Key Encryption (HPKE) RFC 9180.

Primitives and schemes are based on details in https://www.rfc-editor.org/rfc/rfc9180.html.

For simplicity and to accommodate Proof Frog's grammar, the following changes have been made:
- Serializing and deserializing public keys are omitted
- Unused optional parameters are omitted
- LabeledExtract and LabeledExpand are omitted
- Concatenation is replaced with tuples
- Byte strings are replaced with bit strings