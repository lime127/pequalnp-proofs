import PEqualNP.Defs

-- Adapted from R_meta_2071_926 at revision cc5bff61fdb650a4ecd82694aeffa0f790a01a60.
-- Changed to prove exactly the first child of R_meta_2071_587, without extra hypotheses.
-- Original and adapted source are provided under the repository Apache-2.0 license.

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Research.LineSingleBridge :
∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 : ℕ → Bool),   x3 ≠ x4 →     (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x7]? = Option.some x8 → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x8.inputs = [x10, x11] ∧ x10 ≠ x11 ∧ x10 < x1 + x7 ∧ x11 < x1 + x7) →       ((∀ x8 < x1, x5 x8 = Decidable.decide (x8 = ↑x4)) ∧           have x8 : List Bool := x2.wires (List.ofFn fun (x8 : Fin x1) => Decidable.decide (x8 = x3));           ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate) (x11 x12 : ℕ), x2.gates[x9]? = Option.some x10 → x10.inputs = [x11, x12] → (x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 (x1 + x9) = (x8.getD x11 Bool.false && x5 x12 || x5 x11 && x8.getD x12 Bool.false)) ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 (x1 + x9) = (x5 x11 || x5 x12))) →         PEqualNP.ReadK.lineSingle x2 x1 (fun (x9 : ℕ) => Decidable.decide (x9 = ↑x4)) ↑x3 ↑x4 = Bool.true → x5 x2.output = Bool.true := by
  classical
  let gateStep {α : Type} (op : GateOp → List α → α) (dflt : α)
      (ws : List α) (g : Gate) : List α :=
    ws ++ [op g.op (g.inputs.map fun i => ws.getD i dflt)]

  have gateStep_length {α : Type} (op : GateOp → List α → α) (dflt : α) (ws : List α) (g : Gate) :
      (gateStep op dflt ws g).length = ws.length + 1 := by
    simp [gateStep]

  have prefix_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (i : ℕ) (hi : i < ws.length) :
      (gs.foldl (gateStep op dflt) ws).getD i dflt = ws.getD i dflt := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by rw [gateStep_length]; omega)]
      simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have wireCount {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) :
      (gs.foldl (gateStep op dflt) ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih, gateStep_length, List.length_cons]
      omega

  have indexed_value {α : Type} (op : GateOp → List α → α) (dflt : α) (gs : List Gate) (ws : List α) (j : ℕ) (g : Gate)
      (hj : gs[j]? = some g) (hback : ∀ i ∈ g.inputs, i < ws.length + j) :
      (gs.foldl (gateStep op dflt) ws).getD (ws.length + j) dflt =
        op g.op (g.inputs.map fun i => (gs.foldl (gateStep op dflt) ws).getD i dflt) := by
    induction gs generalizing ws j with
    | nil => simp at hj
    | cons g0 gs ih =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst g0
        rw [Nat.add_zero, List.foldl_cons, prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
        have hstep : (gateStep op dflt ws g).getD ws.length dflt =
            op g.op (g.inputs.map fun i => ws.getD i dflt) := by
          simp only [gateStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl ws.length)]
          simp
        rw [hstep]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlt : i < ws.length := by simpa using hback i hi
        rw [prefix_value _ _ _ _ _ (by rw [gateStep_length]; omega)]
        simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hj
        rw [List.foldl_cons]
        have hidx : ws.length + (j + 1) = (gateStep op dflt ws g0).length + j := by
          rw [gateStep_length]
          omega
        rw [hidx]
        exact ih (gateStep op dflt ws g0) j hj (by simpa only [hidx] using hback)

  let Valid (n : ℕ) (C : Circuit) : Prop :=
    ∀ j g, C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
        g.inputs = [a,b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j

  let val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD i false

  have val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
      val C x i = x ⟨i,hi⟩ := by
    have hi' : i < (List.ofFn x).length := by simpa using hi
    change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = _
    rw [prefix_value _ _ _ _ _ hi', List.getD_eq_getElem _ _ hi', List.getElem_ofFn]

  have val_outside {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ)
      (hi : n + C.gates.length ≤ i) : val C x i = false := by
    change (C.gates.foldl (gateStep GateOp.eval false) (List.ofFn x)).getD i false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simpa only [wireCount, List.length_ofFn] using hi

  have val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hj : C.gates[j]? = some g) (a b : ℕ) (hg : g.inputs = [a,b])
      (ha : a < n + j) (hb : b < n + j) :
      (g.op = .and → val C x (n + j) = (val C x a && val C x b)) ∧
      (g.op = .or → val C x (n + j) = (val C x a || val C x b)) := by
    have hback : ∀ i ∈ g.inputs, i < (List.ofFn x).length + j := by
      simp only [hg, List.length_ofFn, List.mem_cons, List.not_mem_nil, or_false]
      rintro i (rfl | rfl) <;> assumption
    have hv := indexed_value GateOp.eval false C.gates (List.ofFn x) j g hj hback
    simp only [List.length_ofFn, hg, List.map_cons, List.map_nil] at hv
    constructor
    · intro ho
      rw [ho] at hv
      change val C x (n+j) = (val C x a && (val C x b && true)) at hv
      simpa only [Bool.and_true] using hv
    · intro ho
      rw [ho] at hv
      change val C x (n+j) = (val C x a || (val C x b || false)) at hv
      simpa only [Bool.or_false] using hv

  let oneInput (n z : ℕ) : Fin n → Bool :=
    fun i => decide (i.val = z)

  let twoInputs (n p l : ℕ) : Fin n → Bool :=
    fun i => decide (i.val = p ∨ i.val = l)

  let LinearTrace (n : ℕ) (C : Circuit) (other repeated : ℕ) (R : ℕ → Bool) : Prop :=
    (∀ i < n, R i = decide (i = repeated)) ∧
    ∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
      (g.op = .and →
        R (n + j) =
          ((val C (oneInput n other) a && R b) || (R a && val C (oneInput n other) b))) ∧
      (g.op = .or → R (n + j) = (R a || R b))


  let linearOp (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
    GateOp.rec (motive := fun _ => Bool × Bool)
      (ins.foldl (fun acc p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false))
      (ins.any (·.1), ins.any (·.2)) (false,false) (fun _ => (false,false))
      (false,false) op

  have lineSingle_eq_trace (n : ℕ) (C : Circuit) (hC : Valid n C) (other repeated : ℕ)
      (hne : other ≠ repeated) (R : ℕ → Bool) (hR : LinearTrace n C other repeated R)
      (hout : C.output < n + C.gates.length) :
      PEqualNP.ReadK.lineSingle C n (fun i => decide (i = repeated)) other repeated = R C.output := by
    let x := (List.range n).map fun i => i == other || i == repeated
    let start : List (Bool × Bool) :=
      (x.zipIdx).map fun bi => if decide (bi.2 = repeated) then (false,bi.1) else (bi.1,false)
    let W := C.gates.foldl (gateStep linearOp (false,false)) start
    let S := val C (oneInput n other)
    have hlen : start.length = n := by simp [start, x]
    have hparts : ∀ i < n + C.gates.length,
        (W.getD i (false,false)).1 = S i ∧ (W.getD i (false,false)).2 = R i := by
      intro i
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        intro hi
        by_cases hin : i < n
        · have hi' : i < start.length := by rwa [hlen]
          have hx : i < x.length := by simpa [x] using hin
          have hx' : x[i] = (i == other || i == repeated) := by simp [x]
          have h0 : (W.getD i (false,false)) =
              (if decide (i = repeated) then (false,x[i]) else (x[i],false)) := by
            rw [show W.getD i (false,false) = start.getD i (false,false) from
              prefix_value linearOp _ C.gates start i hi', List.getD_eq_getElem _ _ hi']
            simp [start, List.getElem_zipIdx]
          have hS : S i = decide (i = other) := val_input C (oneInput n other) i hin
          rw [h0, hS, hR.1 i hin, hx']
          by_cases hr : i = repeated
          · simp [hr,Ne.symm hne]
          · by_cases ho : i = other <;> simp [hr,ho,hne]
        · let j := i - n
          have heq : i = n + j := by dsimp [j]; omega
          have hj : j < C.gates.length := by omega
          let g := C.gates[j]
          have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
          obtain ⟨hop, a, b, hinp, _, ha, hb⟩ := hC j g hg
          have ha' := ih a (by omega) (by omega)
          have hb' := ih b (by omega) (by omega)
          have hback : ∀ k ∈ g.inputs, k < start.length + j := by
            simp only [hlen, hinp, List.mem_cons, List.not_mem_nil, or_false]
            rintro k (rfl | rfl) <;> assumption
          have hW := indexed_value linearOp (false,false) C.gates start j g hg hback
          change W.getD (start.length + j) (false,false) =
            linearOp g.op (g.inputs.map fun k => W.getD k (false,false)) at hW
          rw [hlen, ← heq, hinp, List.map_cons, List.map_cons, List.map_nil] at hW
          have ha'' : W.getD a (false,false) = (S a, R a) := Prod.ext ha'.1 ha'.2
          have hb'' : W.getD b (false,false) = (S b, R b) := Prod.ext hb'.1 hb'.2
          rw [ha'', hb''] at hW
          have hv := val_gate C (oneInput n other) j g hg a b hinp ha hb
          have hr := hR.2 j g a b hg hinp
          rw [← heq] at hv hr
          rcases hop with hop | hop
          · rw [hop] at hW
            rw [hW]
            exact ⟨by simpa [linearOp, S] using (hv.1 hop).symm, by
              simpa [linearOp, S] using (hr.1 hop).symm⟩
          · rw [hop] at hW
            rw [hW]
            exact ⟨by simpa [linearOp, S] using (hv.2 hop).symm, by
              simpa [linearOp, S] using (hr.2 hop).symm⟩
    have hfold : PEqualNP.ReadK.linearParts C (fun i => decide (i = repeated)) x = W := by
      change PEqualNP.ReadK.linearParts C (fun i => decide (i = repeated)) x =
        C.gates.foldl (gateStep linearOp (false,false)) start
      unfold PEqualNP.ReadK.linearParts gateStep start
      congr 1
      funext ws g
      cases g.op <;> rfl
    unfold PEqualNP.ReadK.lineSingle
    change ((PEqualNP.ReadK.linearParts C (fun i => decide (i = repeated)) x).getD
      C.output (false,false)).2 = R C.output
    rw [hfold]
    exact (hparts C.output hout).2

  intro n C a b d hab hgates hd hs
  have hone : oneInput n a.val = (fun i : Fin n => decide (i = a)) := by
    funext i
    simp only [oneInput, Fin.ext_iff]
  have htrace : LinearTrace n C a.val b.val d := by
    refine ⟨hd.1, ?_⟩
    simpa only [val, hone] using hd.2
  have hlen : (PEqualNP.ReadK.linearParts C (fun i => decide (i = b.val))
      ((List.range n).map fun i => i == a.val || i == b.val)).length = n + C.gates.length := by
    let xs := (List.range n).map fun i => i == a.val || i == b.val
    let init : List (Bool × Bool) :=
      (xs.zipIdx).map fun bi => if decide (bi.2 = b.val) then (false, bi.1) else (bi.1, false)
    have heq : PEqualNP.ReadK.linearParts C (fun i => decide (i = b.val)) xs =
        C.gates.foldl (gateStep linearOp (false, false)) init := by
      unfold PEqualNP.ReadK.linearParts gateStep init
      congr 1
      funext ws g
      cases g.op <;> rfl
    change (PEqualNP.ReadK.linearParts C (fun i => decide (i = b.val)) xs).length = _
    rw [heq, wireCount]
    simp [init, xs]
  have hout : C.output < n + C.gates.length := by
    by_contra h
    have hdefault := List.getD_eq_default
      (PEqualNP.ReadK.linearParts C (fun i => decide (i = b.val))
        ((List.range n).map fun i => i == a.val || i == b.val))
      (false, false) (show (PEqualNP.ReadK.linearParts C (fun i => decide (i = b.val))
        ((List.range n).map fun i => i == a.val || i == b.val)).length ≤ C.output by omega)
    unfold PEqualNP.ReadK.lineSingle at hs
    rw [hdefault] at hs
    contradiction
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have heq := lineSingle_eq_trace n C hgates a.val b.val hne d htrace hout
  rw [heq] at hs
  exact hs
