# Contributing

Contributions that improve exposition, portability, or proof structure are
welcome. Please keep the following invariants:

1. Do not introduce `sorry`, new axioms, `native_decide`, or `unsafe` into the
   authenticated proof path.
2. Regenerate and authenticate the V97 manifest after changing generated
   sources.
3. Run the nearest leaf build first, then its aggregate, and finally the public
   endpoint.
4. Keep generated proofs deterministic and fail closed on source drift.
5. Separate mathematical changes from bulk regeneration whenever possible.

For a pull request, include the exact Lean version, the commands run, and the
relevant `#print axioms` output.

