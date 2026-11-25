import PEqualNP.Defs.ReadK

/-!
OR frontiers preserve both Boolean values and single-occurrence coefficients.
A frontier expands OR gates and stops at every other gate, retaining the wire
identity of each stopped gate. In particular, this does not simplify AND(u,u).
This is infrastructure for the Circuit-to-two-AND-normal-form bridge; it does
not prove CHILD2 or a circuit-size lower bound.

The append-only evaluator lemmas are adapted from R_meta_2071_926 at
cc5bff61fdb650a4ecd82694aeffa0f790a01a60 and LineSingleBridge, under the
repository Apache-2.0 license. The indexed operator and frontier results are
new adaptations of that proof pattern.
-/
namespace PEqualNP.Research.ORFrontier
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def step {α : Type} (op : ℕ → GateOp → List α → α) (dflt : α)
    (ws : List α) (g : Gate) : List α :=
  ws ++ [op ws.length g.op (g.inputs.map fun i => ws.getD i dflt)]

theorem step_length {α : Type} (op : ℕ → GateOp → List α → α) (dflt : α)
    (ws : List α) (g : Gate) : (step op dflt ws g).length = ws.length + 1 := by
  simp [step]

theorem prefix_value {α : Type} (op : ℕ → GateOp → List α → α) (dflt : α)
    (gs : List Gate) (ws : List α) (i : ℕ) (hi : i < ws.length) :
    (gs.foldl (step op dflt) ws).getD i dflt = ws.getD i dflt := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [step_length]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wire_count {α : Type} (op : ℕ → GateOp → List α → α) (dflt : α)
    (gs : List Gate) (ws : List α) :
    (gs.foldl (step op dflt) ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, step_length, List.length_cons]
    omega

theorem indexed_value {α : Type} (op : ℕ → GateOp → List α → α) (dflt : α)
    (gs : List Gate) (ws : List α) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) (hback : ∀ i ∈ g.inputs, i < ws.length + j) :
    (gs.foldl (step op dflt) ws).getD (ws.length + j) dflt =
      op (ws.length + j) g.op
        (g.inputs.map fun i => (gs.foldl (step op dflt) ws).getD i dflt) := by
  induction gs generalizing ws j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst g0
      rw [Nat.add_zero, List.foldl_cons,
        prefix_value _ _ _ _ _ (by rw [step_length]; omega)]
      have hstep : (step op dflt ws g).getD ws.length dflt =
          op ws.length g.op (g.inputs.map fun i => ws.getD i dflt) := by
        simp only [step, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl ws.length)]
        simp
      rw [hstep]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hlt : i < ws.length := by simpa using hback i hi
      rw [prefix_value _ _ _ _ _ (by rw [step_length]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      rw [List.foldl_cons]
      have hidx : ws.length + (j+1) = (step op dflt ws g0).length + j := by
        rw [step_length]
        omega
      rw [hidx]
      exact ih (step op dflt ws g0) j hj (by simpa only [hidx] using hback)

def frontierOp (w : ℕ) (op : GateOp) (ins : List (List ℕ)) : List ℕ :=
  match op with
  | .or => ins.flatten
  | _ => [w]

/-- OR expansion with multiplicities retained. Repeated OR atoms are harmless;
AND wire identities are never merged or contracted. -/
def frontiers (C : Circuit) (n : ℕ) : List (List ℕ) :=
  C.gates.foldl (step frontierOp []) ((List.range n).map fun i => [i])

def frontier (C : Circuit) (n w : ℕ) : List ℕ :=
  (frontiers C n).getD w []

def ReadsBack (C : Circuit) (n : ℕ) : Prop :=
  ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n+j

theorem frontier_input (C : Circuit) (n i : ℕ) (hi : i < n) :
    frontier C n i = [i] := by
  unfold frontier frontiers
  rw [prefix_value _ _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem frontier_gate (C : Circuit) (n j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hb : ∀ i ∈ g.inputs, i < n+j) :
    frontier C n (n+j) = frontierOp (n+j) g.op
      (g.inputs.map fun i => frontier C n i) := by
  have h := indexed_value frontierOp [] C.gates
    ((List.range n).map fun i => [i]) j g hg (by simpa using hb)
  simpa [frontier, frontiers] using h

/-- Any wire assignment satisfying the OR recurrence is recovered by taking
OR over its frontier. No condition is imposed on the non-OR operations. -/
theorem any_eq (C : Circuit) (n : ℕ) (hb : ReadsBack C n) (v : ℕ → Bool)
    (hor : ∀ j g, C.gates[j]? = some g → g.op = .or →
      v (n+j) = (g.inputs.map v).any id) :
    ∀ w, w < n+C.gates.length → (frontier C n w).any v = v w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [frontier_input C n w hin]
      simp
    · let j := w-n
      have heq : w = n+j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
      have hback := hb j g hg
      rw [heq, frontier_gate C n j g hg hback]
      cases hop : g.op with
      | or =>
        rw [hor j g hg hop]
        simp only [frontierOp, List.any_flatten, List.any_map]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, Function.comp_apply, id_eq]
        constructor
        · rintro ⟨i, hi, h⟩
          exact ⟨i, hi, (ih i (by have := hback i hi; omega)
            (by have := hback i hi; omega)) ▸ (List.any_eq_true.mpr h)⟩
        · rintro ⟨i, hi, h⟩
          exact ⟨i, hi, List.any_eq_true.mp ((ih i (by have := hback i hi; omega)
            (by have := hback i hi; omega)).symm ▸ h)⟩
      | and | not | mod m | maj => simp [frontierOp]

/-- A frontier atom is an original input or a genuine non-OR gate output,
and never lies later than the wire whose frontier is being expanded. -/
theorem atom_support (C : Circuit) (n : ℕ) (hb : ReadsBack C n) :
    ∀ w, w < n+C.gates.length → ∀ r ∈ frontier C n w,
      r ≤ w ∧ (r < n ∨ ∃ j g, r = n+j ∧ C.gates[j]? = some g ∧ g.op ≠ .or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw r hr
    by_cases hin : w < n
    · rw [frontier_input C n w hin] at hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨le_rfl, Or.inl hin⟩
    · let j := w-n
      have heq : w = n+j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
      have hback := hb j g hg
      rw [heq, frontier_gate C n j g hg hback] at hr
      cases hop : g.op with
      | or =>
        simp only [frontierOp, hop, List.mem_flatten, List.mem_map] at hr
        obtain ⟨rs, ⟨i, hi, rfl⟩, hr⟩ := hr
        have hiw : i < w := by have := hback i hi; omega
        obtain ⟨hle, hs⟩ := ih i hiw (by omega) r hr
        exact ⟨by omega, hs⟩
      | and | not | mod m | maj =>
        simp only [frontierOp, hop, List.mem_singleton] at hr
        refine ⟨by omega, Or.inr ⟨j, g, hr, hg, ?_⟩⟩
        simp [hop]

def value (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

theorem value_or (C : Circuit) (x : List Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hb : ∀ i ∈ g.inputs, i < x.length+j)
    (ho : g.op = .or) :
    value C x (x.length+j) = (g.inputs.map (value C x)).any id := by
  have h := indexed_value (fun _ => GateOp.eval) false C.gates x j g hg hb
  change value C x (x.length+j) =
    GateOp.eval g.op (g.inputs.map (value C x)) at h
  simpa [ho, GateOp.eval] using h

/-- Actual Circuit.wires values are preserved by OR expansion. -/
theorem value_eq_frontier (C : Circuit) (x : List Bool)
    (hb : ReadsBack C x.length) (w : ℕ) (hw : w < x.length+C.gates.length) :
    value C x w = (frontier C x.length w).any (value C x) := by
  symm
  exact any_eq C x.length hb (value C x)
    (fun j g hg ho => value_or C x j g hg (hb j g hg) ho) w hw


def linearOp (_ : ℕ) (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | .and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | .or => (ins.any (·.1), ins.any (·.2))
  | _ => (false, false)

def parts (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) (w : ℕ) : Bool × Bool :=
  (PEqualNP.ReadK.linearParts C isLine x).getD w (false, false)

theorem parts_fold (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts C isLine x =
      C.gates.foldl (step linearOp (false, false))
        ((x.zipIdx).map fun bi => if isLine bi.2 then (false, bi.1) else (bi.1, false)) := by
  unfold PEqualNP.ReadK.linearParts step
  congr 1
  funext ws g
  cases g.op <;> rfl

theorem parts_or (C : Circuit) (isLine : ℕ → Bool) (x : List Bool)
    (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
    (hb : ∀ i ∈ g.inputs, i < x.length+j) (ho : g.op = .or) :
    parts C isLine x (x.length+j) =
      ((g.inputs.map fun i => parts C isLine x i).any (·.1),
       (g.inputs.map fun i => parts C isLine x i).any (·.2)) := by
  let start := (x.zipIdx).map fun bi =>
    if isLine bi.2 then (false, bi.1) else (bi.1, false)
  have hlen : start.length = x.length := by simp [start]
  have h := indexed_value linearOp (false, false) C.gates start j g hg
    (by simpa only [hlen] using hb)
  rw [hlen, ho] at h
  simpa only [parts, parts_fold, start, linearOp] using h

/-- The first and single-occurrence parts are both preserved by OR expansion.
The isLine predicate is arbitrary; no partition or singleton predicate is
silently substituted. -/
theorem parts_eq_frontier (C : Circuit) (isLine : ℕ → Bool) (x : List Bool)
    (hb : ReadsBack C x.length) (w : ℕ) (hw : w < x.length+C.gates.length) :
    parts C isLine x w =
      ((frontier C x.length w).any fun i => (parts C isLine x i).1,
       (frontier C x.length w).any fun i => (parts C isLine x i).2) := by
  apply Prod.ext
  · symm
    apply any_eq C x.length hb (fun i => (parts C isLine x i).1) ?_ w hw
    intro j g hg ho
    rw [parts_or C isLine x j g hg (hb j g hg) ho]
    simp [List.any_map, Function.comp_def]
  · symm
    apply any_eq C x.length hb (fun i => (parts C isLine x i).2) ?_ w hw
    intro j g hg ho
    rw [parts_or C isLine x j g hg (hb j g hg) ho]
    simp [List.any_map, Function.comp_def]

/-- In an AND/OR circuit, the retained non-input atoms are exactly AND outputs. -/
theorem atom_support_ao (C : Circuit) (n : ℕ) (hb : ReadsBack C n)
    (hao : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and ∨ g.op = .or)
    (w : ℕ) (hw : w < n+C.gates.length) (r : ℕ) (hr : r ∈ frontier C n w) :
    r ≤ w ∧ (r < n ∨ ∃ j g, r = n+j ∧ C.gates[j]? = some g ∧ g.op = .and) := by
  obtain ⟨hle, hs⟩ := atom_support C n hb w hw r hr
  refine ⟨hle, ?_⟩
  rcases hs with hi | ⟨j, g, heq, hg, hno⟩
  · exact Or.inl hi
  · refine Or.inr ⟨j, g, heq, hg, ?_⟩
    exact (hao j g hg).resolve_right hno

end PEqualNP.Research.ORFrontier

#print axioms PEqualNP.Research.ORFrontier.atom_support_ao
#print axioms PEqualNP.Research.ORFrontier.parts_eq_frontier

#print axioms PEqualNP.Research.ORFrontier.atom_support
#print axioms PEqualNP.Research.ORFrontier.value_eq_frontier
