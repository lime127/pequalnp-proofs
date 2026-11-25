import PEqualNP.Defs

namespace Lime127.Research.Mask4974

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [5, 8]⟩,
    ⟨.and, [9, 10]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [5, 6]⟩,
    ⟨.or, [3, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [11, 15]⟩], 16⟩

lemma upper : PEqualNP.Represents.RepSizeAtMost
    (fun u v : Fin 4 => (4974 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end Lime127.Research.Mask4974
