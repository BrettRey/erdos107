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

/-- A version of the 2D Carathéodory step specialized to images of a finite set of indices. -/
lemma mem_convexHull_image_finset_card_le_three {N : ℕ} {p : Fin N → Plane} {s : Set (Fin N)}
    {i : Fin N} (hx : p i ∈ convexHull ℝ (p '' s)) :
    ∃ u : Finset (Fin N),
      (↑u : Set (Fin N)) ⊆ s ∧ u.card ≤ 3 ∧ p i ∈ convexHull ℝ (p '' (↑u : Set (Fin N))) := by
  classical
  obtain ⟨t, ht, hcard, hx_t⟩ :=
    mem_convexHull_finset_card_le_three (s := p '' s) (x := p i) hx
  -- Choose indices for each point in the small finset.
  let g : t → Fin N := fun x => Classical.choose (ht x.2)
  have hg_mem : ∀ x : t, g x ∈ s := by
    intro x
    exact (Classical.choose_spec (ht x.2)).1
  have hg_eq : ∀ x : t, p (g x) = x := by
    intro x
    exact (Classical.choose_spec (ht x.2)).2
  let u : Finset (Fin N) := t.attach.image (fun x => g x)
  have hu_sub : (↑u : Set (Fin N)) ⊆ s := by
    intro j hj
    have hj' : j ∈ u := by simpa using hj
    rcases Finset.mem_image.1 hj' with ⟨x, hx, rfl⟩
    exact hg_mem x
  have hcard_u : u.card ≤ 3 := by
    have : u.card ≤ t.attach.card := by
      simpa [u] using (Finset.card_image_le (f := g) (s := t.attach))
    have hta : t.attach.card = t.card := by simp
    exact (le_trans (by simpa [hta] using this) hcard)
  have ht_sub : (↑t : Set Plane) ⊆ p '' (↑u : Set (Fin N)) := by
    intro x hx
    refine ⟨g ⟨x, hx⟩, ?_, ?_⟩
    · have : g ⟨x, hx⟩ ∈ u := by
        refine Finset.mem_image.2 ?_
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
      simpa using this
    · simpa using hg_eq ⟨x, hx⟩
  have hx_u : p i ∈ convexHull ℝ (p '' (↑u : Set (Fin N))) :=
    convexHull_mono ht_sub hx_t
  exact ⟨u, hu_sub, hcard_u, hx_u⟩



/-- For convex-independent indexed points, convex-hull membership equals index membership. -/
lemma convexIndependent_mem_convexHull_iff {N : ℕ} {p : Fin N → Plane}
    (hp : ConvexIndependent ℝ p) (s : Set (Fin N)) (i : Fin N) :
    p i ∈ convexHull ℝ (p '' s) ↔ i ∈ s := by
  simpa using (ConvexIndependent.mem_convexHull_iff (p := p) hp s i)

/-- A convex-independent point is not in the convex hull of the other indices. -/
lemma convexIndependent_not_mem_convexHull_diff {N : ℕ} {p : Fin N → Plane}
    (hp : ConvexIndependent ℝ p) (i : Fin N) (s : Set (Fin N)) :
    p i ∉ convexHull ℝ (p '' (s \ {i})) := by
  exact (convexIndependent_iff_notMem_convexHull_diff (p := p)).1 hp i s
end

end ErdosSzekeres
