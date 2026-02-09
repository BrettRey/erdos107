/-
  Erdős Problem #107: Erdős–Szekeres Conjecture

  Conjecture: ES(n) = 2^(n-2) + 1

  where ES(n) is the minimum number of points in general position (no three
  collinear) in the plane that guarantees the existence of n points in
  convex position.

  Known results:
  - ES(3) = 3 (trivial)
  - ES(4) = 5 (Esther Klein, 1935)
  - ES(5) = 9 (Makai, 1935)
  - ES(6) = 17 (Szekeres & Peters, 2006, SAT-based)
  - ES(7) = 33 (conjectured)

  This file defines the core concepts needed to state and approach the problem.
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Independent
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

open Set
open scoped Pointwise

noncomputable section

namespace ErdosSzekeres

/-- The plane ℝ² as our ambient space -/
abbrev Plane := Fin 2 → ℝ

variable {s : Set Plane}

/-- A set of points is in **general position** if every triple is affinely independent
    (equivalently, no three points are collinear). -/
def GeneralPosition (s : Set Plane) : Prop :=
  ∀ ⦃a b c : Plane⦄,
    a ∈ s → b ∈ s → c ∈ s →
    a ≠ b → a ≠ c → b ≠ c →
    AffineIndependent ℝ ![a, b, c]

/-- A finite set of points is in **convex position** if every point is a vertex of
    the convex hull (i.e., no point lies in the convex hull of the others).
    This is equivalent to convex independence. -/
def ConvexPosition (s : Set Plane) : Prop :=
  ConvexIndependent ℝ (fun p : s => (p : Plane))

/-- Indexed version: `N` labelled points in general position (no three collinear). -/
def GeneralPositionFn {N : ℕ} (p : Fin N → Plane) : Prop :=
  ∀ i j k : Fin N, i ≠ j → i ≠ k → j ≠ k →
    AffineIndependent ℝ ![p i, p j, p k]

/-- Indexed version: contains `n` points in convex position via an injection of indices. -/
def HasConvexSubset {n N : ℕ} (p : Fin N → Plane) : Prop :=
  ∃ f : Fin n ↪ Fin N, ConvexIndependent ℝ (p ∘ f)

/-- Indexed witness: for labelled `N`-point configurations, general position forces an
    `n`-point convex-position subset. -/
def ESWitnessFn (n N : ℕ) : Prop :=
  ∀ p : Fin N → Plane, GeneralPositionFn p → HasConvexSubset (n := n) p

/-- GeneralPositionFn is preserved under reindexing by an embedding. -/
lemma GeneralPositionFn.comp {N M : ℕ} {p : Fin M → Plane} (f : Fin N ↪ Fin M)
    (hp : GeneralPositionFn p) : GeneralPositionFn (p ∘ f) := by
  intro i j k hij hik hjk
  exact hp (f i) (f j) (f k)
    (by
      intro h
      exact hij (f.injective h))
    (by
      intro h
      exact hik (f.injective h))
    (by
      intro h
      exact hjk (f.injective h))

/-- Monotonicity in `N` for the indexed witness predicate. -/
lemma ESWitnessFn.mono {n N N' : ℕ} (hNN' : N ≤ N') (h : ESWitnessFn n N) :
    ESWitnessFn n N' := by
  intro p hp
  let f : Fin N ↪ Fin N' := Fin.castLEEmb hNN'
  have hp' : GeneralPositionFn (p ∘ f) :=
    GeneralPositionFn.comp (p := p) f hp
  rcases h (p ∘ f) hp' with ⟨g, hg⟩
  let fg : Fin n ↪ Fin N' :=
    ⟨fun i => f (g i), by
      intro i j h
      exact g.injective (f.injective h)⟩
  refine ⟨fg, ?_⟩
  -- `hg` is about `(p ∘ f) ∘ g`; the goal is about `p ∘ fg`.
  simpa [fg, Function.comp] using hg

/-- Lift a convex subset from a reindexed configuration back to the original one. -/
lemma HasConvexSubset.of_reindex {n N M : ℕ} {p : Fin M → Plane} (f : Fin N ↪ Fin M) :
    HasConvexSubset (n := n) (p ∘ f) → HasConvexSubset (n := n) p := by
  rintro ⟨g, hg⟩
  let fg : Fin n ↪ Fin M :=
    ⟨fun i => f (g i), by
      intro i j h
      exact g.injective (f.injective h)⟩
  refine ⟨fg, ?_⟩
  simpa [fg, Function.comp] using hg

/-- GeneralPosition is preserved under subsets. -/
lemma GeneralPosition.mono {s t : Set Plane} (ht : t ⊆ s) (hs : GeneralPosition s) :
    GeneralPosition t := by
  intro a b c ha hb hc hneab hneac hnebc
  exact hs (ht ha) (ht hb) (ht hc) hneab hneac hnebc

/-- ConvexPosition is preserved under subsets. -/
lemma ConvexPosition.mono {s t : Set Plane} (ht : t ⊆ s) (hs : ConvexPosition s) :
    ConvexPosition t := by
  -- Use ConvexIndependent.mono on the underlying set-of-points formulation.
  simpa [ConvexPosition] using
    (ConvexIndependent.mono (s := t) (t := s) (hc := by simpa [ConvexPosition] using hs) ht)

/-- For three collinear points, one lies in the convex hull of the other two. -/
private lemma collinear_three_mem_convexHull {a b c : Plane}
    (hcol : Collinear ℝ ({a, b, c} : Set Plane)) :
    a ∈ convexHull ℝ ({b, c} : Set Plane) ∨
      b ∈ convexHull ℝ ({a, c} : Set Plane) ∨
      c ∈ convexHull ℝ ({a, b} : Set Plane) := by
  classical
  rcases (collinear_iff_exists_forall_eq_smul_vadd (k := ℝ) (s := ({a, b, c} : Set Plane))).1 hcol with
    ⟨p0, v, hv⟩
  rcases hv a (by simp) with ⟨ra, rfl⟩
  rcases hv b (by simp) with ⟨rb, rfl⟩
  rcases hv c (by simp) with ⟨rc, rfl⟩

  have mem_between :
      ∀ {r1 r2 r3 : ℝ},
        r1 ≤ r2 → r2 ≤ r3 →
          (r2 • v + p0) ∈ convexHull ℝ ({r1 • v + p0, r3 • v + p0} : Set Plane) := by
    intro r1 r2 r3 h1 h2
    by_cases hne : r1 = r3
    · have hr2 : r2 = r1 := by linarith [h1, h2, hne]
      subst r3
      subst r2
      have : (r1 • v + p0) ∈ segment ℝ (r1 • v + p0) (r1 • v + p0) := by
        simpa using (left_mem_segment ℝ (r1 • v + p0) (r1 • v + p0))
      simpa [convexHull_pair] using this
    · have hle : r1 ≤ r3 := le_trans h1 h2
      have hlt : r1 < r3 := lt_of_le_of_ne hle hne
      have hdenom : 0 < r3 - r1 := sub_pos.mpr hlt
      let t : ℝ := (r2 - r1) / (r3 - r1)
      have ht0 : 0 ≤ t := by
        have hnum : 0 ≤ r2 - r1 := sub_nonneg.mpr h1
        exact div_nonneg hnum (le_of_lt hdenom)
      have ht1 : t ≤ 1 := by
        have hnum : r2 - r1 ≤ r3 - r1 := sub_le_sub_right h2 _
        have : (r2 - r1) / (r3 - r1) ≤ 1 := (div_le_one hdenom).2 hnum
        simpa [t] using this
      have ht : t * (r3 - r1) = r2 - r1 := by
        have hdenom' : r3 - r1 ≠ 0 := by linarith
        dsimp [t]
        field_simp [hdenom']
      have hr2 : r2 = (1 - t) * r1 + t * r3 := by
        calc
          r2 = r1 + (r2 - r1) := by ring
          _ = r1 + t * (r3 - r1) := by simp [ht]
          _ = (1 - t) * r1 + t * r3 := by ring
      have hb_line : r2 • v + p0 = AffineMap.lineMap (r1 • v + p0) (r3 • v + p0) t := by
        -- use lineMap formula in modules
        ext i
        simp [AffineMap.lineMap_apply_module, hr2, vadd_eq_add, smul_add, add_smul, mul_add,
          add_comm, add_left_comm, add_assoc]
        ring
      have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
      have hb_seg : r2 • v + p0 ∈ segment ℝ (r1 • v + p0) (r3 • v + p0) := by
        have : AffineMap.lineMap (r1 • v + p0) (r3 • v + p0) t ∈
            segment ℝ (r1 • v + p0) (r3 • v + p0) := by
          have : AffineMap.lineMap (r1 • v + p0) (r3 • v + p0) t ∈
              AffineMap.lineMap (r1 • v + p0) (r3 • v + p0) '' Icc (0 : ℝ) 1 :=
            mem_image_of_mem _ htIcc
          simpa [segment_eq_image_lineMap] using this
        simpa [hb_line] using this
      simpa [convexHull_pair] using hb_seg

  have hmid :
      (ra ≤ rb ∧ rb ≤ rc) ∨
        (rb ≤ ra ∧ ra ≤ rc) ∨
        (ra ≤ rc ∧ rc ≤ rb) ∨
        (rc ≤ rb ∧ rb ≤ ra) ∨
        (rb ≤ rc ∧ rc ≤ ra) ∨
        (rc ≤ ra ∧ ra ≤ rb) := by
    have h_ab := le_total ra rb
    have h_bc := le_total rb rc
    have h_ac := le_total ra rc
    rcases h_ab with h_ab | h_ab
    · rcases h_bc with h_bc | h_bc
      · exact Or.inl ⟨h_ab, h_bc⟩
      · rcases h_ac with h_ac | h_ac
        · exact Or.inr (Or.inr (Or.inl ⟨h_ac, h_bc⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h_ac, h_ab⟩))))
    · rcases h_bc with h_bc | h_bc
      · rcases h_ac with h_ac | h_ac
        · exact Or.inr (Or.inl ⟨h_ab, h_ac⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h_bc, h_ac⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h_bc, h_ab⟩)))

  rcases hmid with hmid | hmid
  · -- ra ≤ rb ≤ rc
    right; left
    simpa using (mem_between hmid.1 hmid.2)
  · rcases hmid with hmid | hmid
    · -- rb ≤ ra ≤ rc
      left
      simpa using (mem_between hmid.1 hmid.2)
    · rcases hmid with hmid | hmid
      · -- ra ≤ rc ≤ rb
        right; right
        simpa using (mem_between hmid.1 hmid.2)
      · rcases hmid with hmid | hmid
        · -- rc ≤ rb ≤ ra
          right; left
          have hb : (rb • v + p0) ∈ convexHull ℝ ({rc • v + p0, ra • v + p0} : Set Plane) :=
            mem_between hmid.1 hmid.2
          simpa [Set.pair_comm] using hb
        · rcases hmid with hmid | hmid
          · -- rb ≤ rc ≤ ra
            right; right
            have hc : (rc • v + p0) ∈ convexHull ℝ ({rb • v + p0, ra • v + p0} : Set Plane) :=
              mem_between hmid.1 hmid.2
            simpa [Set.pair_comm] using hc
          · -- rc ≤ ra ≤ rb
            left
            have ha : (ra • v + p0) ∈ convexHull ℝ ({rc • v + p0, rb • v + p0} : Set Plane) :=
              mem_between hmid.1 hmid.2
            simpa [Set.pair_comm] using ha

/-- ConvexPosition implies GeneralPosition: if every point is a vertex of the
    convex hull, then no three can be collinear. -/
lemma ConvexPosition.generalPosition (hs : ConvexPosition s) : GeneralPosition s := by
  classical
  intro a b c ha hb hc hneab hneac hnebc
  have hnotmem : ∀ x ∈ s, x ∉ convexHull ℝ (s \ {x}) := by
    simpa [ConvexPosition] using
      (convexIndependent_set_iff_notMem_convexHull_diff (𝕜 := ℝ) (s := s)).1 hs
  have ha_not : a ∉ convexHull ℝ ({b, c} : Set Plane) := by
    intro ha_mem
    have hsubset : ({b, c} : Set Plane) ⊆ s \ {a} := by
      intro x hx
      rcases hx with rfl | rfl
      · exact ⟨hb, by simpa [Set.mem_singleton_iff] using hneab.symm⟩
      · exact ⟨hc, by simpa [Set.mem_singleton_iff] using hneac.symm⟩
    exact (hnotmem a ha) (convexHull_mono hsubset ha_mem)
  have hb_not : b ∉ convexHull ℝ ({a, c} : Set Plane) := by
    intro hb_mem
    have hsubset : ({a, c} : Set Plane) ⊆ s \ {b} := by
      intro x hx
      rcases hx with rfl | rfl
      · exact ⟨ha, by simpa [Set.mem_singleton_iff] using hneab⟩
      · exact ⟨hc, by simpa [Set.mem_singleton_iff] using hnebc.symm⟩
    exact (hnotmem b hb) (convexHull_mono hsubset hb_mem)
  have hc_not : c ∉ convexHull ℝ ({a, b} : Set Plane) := by
    intro hc_mem
    have hsubset : ({a, b} : Set Plane) ⊆ s \ {c} := by
      intro x hx
      rcases hx with rfl | rfl
      · exact ⟨ha, by simpa [Set.mem_singleton_iff] using hneac⟩
      · exact ⟨hb, by simpa [Set.mem_singleton_iff] using hnebc⟩
    exact (hnotmem c hc) (convexHull_mono hsubset hc_mem)
  have hnotcol : ¬ Collinear ℝ ({a, b, c} : Set Plane) := by
    intro hcol
    rcases collinear_three_mem_convexHull hcol with h | h
    · exact ha_not h
    · rcases h with h | h
      · exact hb_not h
      · exact hc_not h
  exact (affineIndependent_iff_not_collinear_set (k := ℝ)).2 hnotcol

namespace Finset

/-- Finset wrapper: general position for a finite set of points. -/
def GeneralPosition (s : Finset Plane) : Prop := by
  classical
  exact ErdosSzekeres.GeneralPosition (s : Set Plane)

/-- Finset wrapper: convex position for a finite set of points. -/
def ConvexPosition (s : Finset Plane) : Prop := by
  classical
  exact ErdosSzekeres.ConvexPosition (s : Set Plane)

/-- Finset.GeneralPosition is preserved under subsets. -/
lemma GeneralPosition.mono {s t : Finset Plane} (ht : t ⊆ s) (hs : GeneralPosition s) :
    GeneralPosition t := by
  classical
  dsimp [GeneralPosition] at hs ⊢
  exact ErdosSzekeres.GeneralPosition.mono (s := (s : Set Plane)) (t := (t : Set Plane))
    (ht := (_root_.Finset.coe_subset).2 ht) hs

/-- Finset.ConvexPosition is preserved under subsets. -/
lemma ConvexPosition.mono {s t : Finset Plane} (ht : t ⊆ s) (hs : ConvexPosition s) :
    ConvexPosition t := by
  classical
  dsimp [ConvexPosition] at hs ⊢
  exact ErdosSzekeres.ConvexPosition.mono (s := (s : Set Plane)) (t := (t : Set Plane))
    (ht := (_root_.Finset.coe_subset).2 ht) hs

end Finset

/-- Witness that ES(n) is well-defined: for every n, there exists some N that works.
    This follows from Ramsey theory. -/
def ESWitness (n N : ℕ) : Prop :=
  by
    classical
    exact
      ∀ (s : Finset Plane),
        s.card = N →
        Finset.GeneralPosition s →
        ∃ t : Finset Plane, t ⊆ s ∧ t.card = n ∧ Finset.ConvexPosition t

lemma ESWitness.mono {n N N' : ℕ} (hNN' : N ≤ N') (h : ESWitness n N) : ESWitness n N' := by
  classical
  intro s hsN' hgp
  have hns : N ≤ s.card := by simpa [hsN'] using hNN'
  obtain ⟨u, hus, hu_card⟩ := _root_.Finset.exists_subset_card_eq (s := s) (n := N) hns
  have hgp_u : Finset.GeneralPosition u :=
    Finset.GeneralPosition.mono (s := s) (t := u) hus hgp
  obtain ⟨t, ht_u, ht_card, ht_conv⟩ := h u (by simpa using hu_card) hgp_u
  refine ⟨t, ?_, ht_card, ht_conv⟩
  intro x hx
  exact hus (ht_u hx)

/-- Witness that ES(n) is well-defined: for every n, there exists some N that works.
    This follows from Ramsey theory. -/
axiom exists_ES_witness (n : ℕ) : ∃ N : ℕ, ESWitness n N

/-- The Erdős–Szekeres number ES(n) is the minimum N such that any set of N points
    in general position in the plane contains n points in convex position. -/
def ES (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_ES_witness n)

lemma ES_spec (n : ℕ) : ESWitness n (ES n) := by
  classical
  simpa [ES] using (Nat.find_spec (exists_ES_witness n))

/-- The Erdős–Szekeres conjecture: ES(n) = 2^(n-2) + 1 for n ≥ 3 -/
def ErdosSzekeresConjecture : Prop :=
  ∀ n : ℕ, n ≥ 3 → ES n = 2^(n-2) + 1

/-- Known lower bound: ES(n) ≥ 2^(n-2) + 1
    (There exist 2^(n-2) points in general position with no convex n-gon) -/
theorem ES_lower_bound (n : ℕ) (hn : n ≥ 3) : ES n ≥ 2^(n-2) + 1 := by
  sorry -- Erdős–Szekeres construction

/-- The ES(6) = 17 theorem (Szekeres & Peters, 2006)
    This was proved via SAT solving. -/
theorem ES_six : ES 6 = 17 := by
  sorry -- SAT-based proof

/-- The ES(7) = 33 conjecture -/
theorem ES_seven : ES 7 = 33 := by
  sorry -- This is what we aim to prove via SAT

end ErdosSzekeres

end -- noncomputable section
