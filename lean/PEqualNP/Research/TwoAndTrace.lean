import Std

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-!
A small algebraic lemma for the second claim's two-AND case.

An OR-only input expression has a pair trace determined by its membership bits
for p and l. Two successive AND gates, with arbitrary OR-only expressions and
optional uses of preceding AND gates between them, have the normal form below.
The bad trace forces the first AND to feed both sides of the second AND and the
second AND to feed the output. Hence both AND values imply the output value.

Scope: this file proves the trace and Boolean normal-form lemmas. It does not
formalize the normalization of an arbitrary Circuit into this representation,
and it does not prove the 64-gate CHILD2 statement.
-/
namespace PEqualNP.Research.TwoAndTrace

/-- Values on the p singleton, l singleton, and pair, followed by the two
single-occurrence coefficients. These use the recursion of ReadK.linearParts. -/
structure Trace where
  point : Bool
  line : Bool
  joint : Bool
  onceP : Bool
  onceL : Bool
  deriving DecidableEq

def leafOr (p l : Bool) : Trace := ⟨p, l, p || l, p, l⟩

def join (a b : Trace) : Trace :=
  ⟨a.point || b.point, a.line || b.line, a.joint || b.joint,
   a.onceP || b.onceP, a.onceL || b.onceL⟩

def meet (a b : Trace) : Trace :=
  ⟨a.point && b.point, a.line && b.line, a.joint && b.joint,
   (a.line && b.onceP) || (a.onceP && b.line),
   (a.point && b.onceL) || (a.onceL && b.point)⟩

def select (use : Bool) (a : Trace) : Trace :=
  ⟨use && a.point, use && a.line, use && a.joint,
   use && a.onceP, use && a.onceL⟩

def outputTrace (ap al bp bl cp cl dp dl ep el uc ud uh uk : Bool) : Trace :=
  let h := meet (leafOr ap al) (leafOr bp bl)
  let k := meet (join (leafOr cp cl) (select uc h))
                (join (leafOr dp dl) (select ud h))
  join (join (leafOr ep el) (select uh h)) (select uk k)

def Bad (t : Trace) : Prop :=
  t.point = false ∧ t.line = false ∧ t.joint = true ∧
  t.onceP = false ∧ t.onceL = false

/-- In this two-AND normal form, a bad pair trace forces both shared uses and
forces the upper AND to reach the output. -/
theorem forcedSharing (ap al bp bl cp cl dp dl ep el uc ud uh uk : Bool)
    (hbad : Bad (outputTrace ap al bp bl cp cl dp dl ep el uc ud uh uk)) :
    uc = true ∧ ud = true ∧ uk = true ∧ uh = false := by
  unfold Bad outputTrace meet join select leafOr at hbad
  dsimp only at hbad
  revert ap al bp bl cp cl dp dl ep el uc ud uh uk
  decide

/-- The Boolean value of the same normal form at any input. -/
def outputValue (a b c d e uc ud uh uk : Bool) : Bool :=
  let h := a && b
  let k := (c || (uc && h)) && (d || (ud && h))
  (e || (uh && h)) || (uk && k)

/-- Both ANDs are clean in the normal form whenever its pair trace is bad.
The five Boolean arguments here can be their values at any assignment. -/
theorem bothAndsClean (ap al bp bl cp cl dp dl ep el uc ud uh uk : Bool)
    (hbad : Bad (outputTrace ap al bp bl cp cl dp dl ep el uc ud uh uk))
    (a b c d e : Bool) :
    ((a && b) = true → outputValue a b c d e uc ud uh uk = true) ∧
    (((c || (uc && (a && b))) && (d || (ud && (a && b)))) = true →
      outputValue a b c d e uc ud uh uk = true) := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := forcedSharing ap al bp bl cp cl dp dl ep el uc ud uh uk hbad
  constructor
  · intro h
    simp [outputValue, h]
  · intro h
    simpa [outputValue] using congrArg (fun z : Bool => e || z) h

end PEqualNP.Research.TwoAndTrace

#print axioms PEqualNP.Research.TwoAndTrace.forcedSharing
#print axioms PEqualNP.Research.TwoAndTrace.bothAndsClean
