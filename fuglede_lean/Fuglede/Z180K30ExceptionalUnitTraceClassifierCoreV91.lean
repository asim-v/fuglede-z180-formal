import Fuglede.Z180K30ExceptionalOrbitSignatureWitnessV78Fix2

/-!
# Unit-only trace classifier core for the framed K30 star (V91)

The finite payload fixes both orbit representatives and varies only the
twelve units of `Z/36Z`.  Translations are deliberately absent: the final
classifier removes them structurally with trace-translation invariance.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30UnitTraceAcceptsBV91
    (o : Fin 7) (r : Fin 8) (unit : RawPoint) : Bool :=
  gramTraceSquare
      (affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r))
      (z180K30ExceptionalOrbitColumnV4
        (z180K30NonHOrbitV78Fix2 o)) ==
    scalarCoeff 936

/-- A rejection leaf says that every one of the twelve units fails the
exact trace-square equation for this fixed pair of orbit representatives. -/
def z180K30UnitTraceRejectAuditV91 (o : Fin 7) (r : Fin 8) : Bool :=
  units36.all fun unit => !z180K30UnitTraceAcceptsBV91 o r unit

/-- Logical semantics of one unit-only rejection certificate. -/
theorem z180K30UnitTraceRejectAudit_semanticsV91
    (o : Fin 7) (r : Fin 8)
    (hreject : z180K30UnitTraceRejectAuditV91 o r = true)
    (unit : RawPoint) (hunit : unit ∈ units36) :
    gramTraceSquare
        (affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r))
        (z180K30ExceptionalOrbitColumnV4
          (z180K30NonHOrbitV78Fix2 o)) ≠
      scalarCoeff 936 := by
  unfold z180K30UnitTraceRejectAuditV91 at hreject
  rw [List.all_eq_true] at hreject
  have hrejectUnit := hreject unit hunit
  intro htrace
  have haccepts : z180K30UnitTraceAcceptsBV91 o r unit = true := by
    simp only [z180K30UnitTraceAcceptsBV91, htrace, beq_self_eq_true]
  simpa only [haccepts, Bool.not_true, Bool.false_eq_true] using hrejectUnit

#print axioms z180K30UnitTraceRejectAudit_semanticsV91

end Fuglede.Z180K30ExceptionalRawV2
