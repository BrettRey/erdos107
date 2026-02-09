import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions

import Erdos107.ErdosSzekeres

namespace ErdosSzekeres

noncomputable section

/-- In `Plane = ℝ²`, any point in the convex hull of a set lies in the convex hull of
    a finite subset of size at most `3`. -/
lemma mem_convexHull_finset_card_le_three {s : Set Plane} {x : Plane}
    (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset Plane,
      (↑t : Set Plane) ⊆ s ∧ t.card ≤ 3 ∧ x ∈ convexHull ℝ (↑t : Set Plane) := by
  classical
  have hx' := hx
  -- unfold the Carathéodory union description
  rw [convexHull_eq_union] at hx'
  rcases Set.mem_iUnion.1 hx' with ⟨t, hx'⟩
  rcases Set.mem_iUnion.1 hx' with ⟨ht, hx'⟩
  rcases Set.mem_iUnion.1 hx' with ⟨ha, hx_t⟩
  have hcard' : t.card ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → Plane))) + 1 := by
    simpa using (AffineIndependent.card_le_finrank_succ (k := ℝ) (p := ((↑) : t → Plane)) ha)
  have hle :
      Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → Plane))) ≤
        Module.finrank ℝ Plane :=
    Submodule.finrank_le _
  have hfinrank : Module.finrank ℝ Plane = 2 := by
    simp [Plane, Module.finrank_pi (R := ℝ) (ι := Fin 2)]
  have hcard : t.card ≤ 3 := by
    nlinarith [hcard', hle, hfinrank]
  exact ⟨t, ht, hcard, hx_t⟩

end

end ErdosSzekeres
