# Contributing

Contributions that improve exposition, portability, or proof structure are
welcome. Please keep the following invariants:

1. Keep the dependency closure of `Fuglede.Z180FugledeTheorem` free of `sorry`,
   `admit`, project-defined axioms, `native_decide`, and `unsafe`.
2. Rebuild and replay `Fuglede.Z180FugledeTheorem` after any mathematical
   change.
3. If a V97 generated source changes, regenerate and authenticate its manifest.
4. Run the nearest leaf build first, then its aggregate, and finally the public
   endpoint.
5. Keep generated proofs deterministic and fail closed on source drift.
6. Separate mathematical changes from bulk regeneration whenever possible.

For a pull request, include the exact Lean version, the commands run, and the
relevant `#print axioms` output.

