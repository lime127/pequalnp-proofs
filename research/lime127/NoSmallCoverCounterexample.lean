import PEqualNP.Outside.L_meta_217

-- Derived result using the existing upstream theorem L_meta_217.
-- This is a research artifact, not an upstream task submission.

theorem Lime127.Research.noSmallCoverCounterexample : ¬ (
∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (t : ℕ), (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧ (∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card = t) ∧ (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → t ≤ T.card) ∧ t ≤ 5 ∧ ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ)) ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) ∧ ∃ I : Finset (Fin gates.length), (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → i ∈ I) ∧ I.card < t
) := by
  classical
  rintro ⟨n, G, hdec, t, hC4, hcover, hmin, ht5,
    gates, out, hbasis, hprior, heval, I, hI, hlt⟩
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, out⟩
  let A : Finset ℕ := I.image (fun i : Fin gates.length => i.val)
  have hmono : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hbasis g hg
    exact ⟨by simpa using hop, Nat.le_of_eq hlen⟩
  have hcomputes : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    change (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩
      (List.ofFn x) = true ↔ _)
    rw [heval x]
    simp only [decide_eq_true_eq]
  have hpositions : ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      C.gates[j]? = some g →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A := by
    intro j g hj hand
    change gates[j]? = some g at hj
    obtain ⟨hjlt, hjget⟩ := List.getElem?_eq_some_iff.mp hj
    have hget : gates.get ⟨j, hjlt⟩ = g := by
      simpa only [List.get_eq_getElem] using hjget
    have hmem : (⟨j, hjlt⟩ : Fin gates.length) ∈ I := by
      apply hI
      rw [hget]
      exact hand
    exact Finset.mem_image.mpr ⟨⟨j, hjlt⟩, hmem, rfl⟩
  have hcard : A.card = I.card := by
    apply Finset.card_image_of_injective
    intro i j hij
    exact Fin.ext hij
  have hbound : t ≤ A.card :=
    PEqualNP.Outside.L_meta_217 n t G C ht5 hC4 hmin hmono hcomputes A hpositions
  rw [hcard] at hbound
  exact (Nat.not_lt_of_ge hbound) hlt
