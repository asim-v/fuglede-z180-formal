# Verification record

## Toolchain

- Lean: `v4.31.0`
- mathlib: `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
- master V97 manifest: `A1A11BF1DB67D0F37A532C44A5F1E62AD208C9229E5F582A85C110B1AC658A40`
- master V97 generator: `1C4BFEE667E3B04CCDC3C5C05DC7E74F841DD89879C813AA14B9DCD5E9F447F7`

## Public endpoints

| Module | Source SHA-256 | Checked object SHA-256 |
| --- | --- | --- |
| `Z180K30ExceptionalProjectiveProfileAggregateV97` | `83C54B8D6BBCE9504EE4AA977BC9B9B421B9348D842D97C28A0FC8C39E962D7C` | `0165B255F75535C004536091E562BB521DCA78A263A5D7AFE63D97E3DE18EE94` |
| `Z180K30CatalogueMasterClosureV81` | `50F50D7D002931FE343D92A8DD7438964A352FE0A8F9EEBF09FF6C067195C428` | `902973D4726CAA8C3044A17772DB4FBD3B443594DBD2171BA60C8BFB500EB02D` |
| `Z180K30UnconditionalCatalogueClosureV96` | `B69FC2F206015BDA5B72172F2CD6F34EFE799BEA8DC73FE573F1D9725F3E49A3` | `9EFA72A5BBF33C0DBD779EB74E88341F86E04481C0C8ACCF596F6DF8FF655B71` |

Each endpoint was built and replayed by `leanchecker`. The final V96 output was:

```text
Fuglede.z180_k30_exceptional_catalogue_completeness_v96
  depends on axioms: [propext, Classical.choice, Quot.sound]
Fuglede.z180_exists_tiling_of_spectral_v96
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Source authentication

Run:

```bash
python scripts/generate_z180_k30_projective_profile_audit_v97.py
```

A successful run prints:

```text
PASS: isolated V97 profile DAG and manifest match exactly
```

The manifest authenticates:

- 946 unique modules in topological order;
- 757 modules in the external algebraic closure;
- 922 build-only modules and 24 checker roots;
- the exact census `16,796 / 213 / 222`;
- child manifests for D4U, D6 algebraic completeness, and D6 validity;
- the ordered V87 catalogue sources and exact witness pointers.

## Trust boundary

The theorem ultimately depends on Lean's kernel, the pinned mathlib sources,
and the standard classical/quotient axioms printed above. Python and
PowerShell generate and orchestrate proof terms, but they are not trusted:
the resulting declarations are elaborated by Lean and replayed by
`leanchecker`.

The proof path does not rely on floating-point arithmetic. It uses integer
polynomials, exact finite lists, ordinary kernel-reduced decisions, and proved
structural aggregation lemmas.

