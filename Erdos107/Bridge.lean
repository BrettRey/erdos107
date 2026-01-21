import Mathlib.Tactic

import Erdos107.ErdosSzekeres
import Erdos107.OrderType
import Erdos107.SATSpec
import Erdos107.SATCNF

namespace ErdosSzekeres

noncomputable section

/-- 2D determinant of two vectors in `Plane = ℝ²`. -/
def det2 (u v : Plane) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- Signed area determinant for a triple of points. -/
def det3 {N : ℕ} (p : Fin N → Plane) (i j k : Fin N) : ℝ :=
  det2 (p j - p i) (p k - p i)

lemma det3_swap12 {N : ℕ} (p : Fin N → Plane) (i j k : Fin N) :
    det3 p j i k = - det3 p i j k := by
  -- coordinate calculation
  simp [det3, det2]
  ring

lemma det3_cycle {N : ℕ} (p : Fin N → Plane) (i j k : Fin N) :
    det3 p i j k = det3 p j k i := by
  -- coordinate calculation
  simp [det3, det2]
  ring

/-- For nonzero `x`, positivity flips under negation (in Bool/`decide` form). -/
lemma decide_pos_eq_not_decide_pos_neg (x : ℝ) (hx : x ≠ 0) :
    decide (x > 0) = ! decide (-x > 0) := by
  classical
  by_cases hxpos : x > 0
  · have hxneg : ¬ (-x > 0) := by
      intro h
      have hxlt : x < 0 := (neg_pos).1 h
      exact lt_asymm hxpos hxlt
    simp [hxpos, hxneg]
  · have hxle : x ≤ 0 := le_of_not_gt hxpos
    have hxlt : x < 0 := lt_of_le_of_ne hxle hx
    have hxnegpos : (-x > 0) := (neg_pos).2 hxlt
    simp [hxpos, hxnegpos]

/-- TODO: geometric lemma: general position implies `det3 ≠ 0` for any distinct triple. -/
lemma det3_ne_zero_of_generalPositionFn {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) {i j k : Fin N} (hijk : Distinct3 i j k) :
    det3 p i j k ≠ 0 := by
  -- Next task: connect `AffineIndependent ℝ ![p i, p j, p k]` to `det3 ≠ 0`.
  sorry

/-- The (abstract) order type induced by a labelled point configuration in general position. -/
def orderTypeOfPoints {N : ℕ} (p : Fin N → Plane) (hp : GeneralPositionFn p) :
    ErdosSzekeres.OrderType N :=
{ σ := fun i j k => decide (det3 p i j k > 0)
, swap12 := by
    intro i j k hijk
    have hdet : det3 p i j k ≠ 0 := det3_ne_zero_of_generalPositionFn (p := p) hp hijk
    have hdec : decide (det3 p i j k > 0) = ! decide (det3 p j i k > 0) := by
      have := decide_pos_eq_not_decide_pos_neg (x := det3 p i j k) hdet
      -- rewrite `- det3 p i j k` as `det3 p j i k`
      simpa [(det3_swap12 (p := p) i j k).symm] using this
    exact hdec
, cycle := by
    intro i j k hijk
    -- no nonzero lemma needed: `det3` is literally invariant under a cyclic shift
    simpa [(det3_cycle (p := p) i j k).symm] }

/-- The induced order type satisfies the rank-3 chirotope (Grassmann–Plücker) axiom scheme. -/
theorem orderTypeOfPoints_isChirotope {N : ℕ} (p : Fin N → Plane) (hp : GeneralPositionFn p) :
    OrderType.IsChirotope (orderTypeOfPoints p hp) := by
  classical
  sorry

/-- The induced order type is acyclic (realizable case). -/
theorem orderTypeOfPoints_acyclic {N : ℕ} (p : Fin N → Plane) (hp : GeneralPositionFn p) :
    OrderType.Acyclic (orderTypeOfPoints p hp) := by
  classical
  sorry

/-- If `p` has an `n`-point convex subset, then the induced order type contains an alternating
    `n`-subset. -/
theorem convexSubset_imp_containsAlternating {n N : ℕ} {p : Fin N → Plane}
    (hp : GeneralPositionFn p) :
    HasConvexSubset (n := n) p →
      OrderType.ContainsAlternating (orderTypeOfPoints p hp) n := by
  classical
  sorry

/-- Conversely: if the induced order type contains an alternating `n`-subset, then `p` has an
    `n`-point convex subset. (This is the geometric content you’ll eventually want.) -/
theorem containsAlternating_imp_convexSubset {n N : ℕ} {p : Fin N → Plane}
    (hp : GeneralPositionFn p) :
    OrderType.ContainsAlternating (orderTypeOfPoints p hp) n →
      HasConvexSubset (n := n) p := by
  classical
  sorry

/-- Geometric counterexamples imply chirotope-level (oriented-matroid-level) counterexamples. -/
theorem geom_counterexample_imp_OM3Counterexample {n N : ℕ} :
    (∃ p : Fin N → Plane, GeneralPositionFn p ∧ ¬ HasConvexSubset (n := n) p) →
      OrderType.OM3Counterexample n N := by
  classical
  rintro ⟨p, hp, hno⟩
  refine ⟨orderTypeOfPoints p hp, orderTypeOfPoints_isChirotope p hp, ?_⟩
  -- show `AvoidsAlternating`
  apply (OrderType.AvoidsAlternating_iff_not_contains (ot := orderTypeOfPoints p hp) n).2
  intro hcontains
  have hconv : HasConvexSubset (n := n) p :=
    containsAlternating_imp_convexSubset (p := p) (hp := hp) hcontains
  exact hno hconv

/-- Geometric counterexamples imply SAT-spec counterexamples (chirotope + acyclic + avoidance). -/
theorem geom_counterexample_imp_SATCounterexample {n N : ℕ} :
    (∃ p : Fin N → Plane, GeneralPositionFn p ∧ ¬ HasConvexSubset (n := n) p) →
      SATCounterexample n N := by
  classical
  rintro ⟨p, hp, hno⟩
  refine ⟨orderTypeOfPoints p hp, ?_⟩
  refine ⟨orderTypeOfPoints_isChirotope p hp, ?_, ?_⟩
  · exact orderTypeOfPoints_acyclic p hp
  · apply (OrderType.AvoidsAlternating_iff_not_contains (ot := orderTypeOfPoints p hp) n).2
    intro hcontains
    have hconv : HasConvexSubset (n := n) p :=
      containsAlternating_imp_convexSubset (p := p) (hp := hp) hcontains
    exact hno hconv

/-- Geometric counterexamples imply satisfiability of the SAT CNF (soundness direction). -/
theorem geom_counterexample_imp_CNF_satisfiable {n N : ℕ} (blocked : List (Fin n ↪ Fin N)) :
    (∃ p : Fin N → Plane, GeneralPositionFn p ∧ ¬ HasConvexSubset (n := n) p) →
      Satisfiable (SATCNF.satSpecCNF n N blocked) := by
  intro hgeom
  exact SATCNF.satCounterexample_imp_satisfiable blocked
    (geom_counterexample_imp_SATCounterexample hgeom)

/-- If there is no chirotope-level counterexample, then there is no geometric counterexample. -/
theorem no_OM3Counterexample_imp_no_geom_counterexample {n N : ℕ} :
    ¬ OrderType.OM3Counterexample n N →
    ¬ (∃ p : Fin N → Plane, GeneralPositionFn p ∧ ¬ HasConvexSubset (n := n) p) := by
  intro hOM hgeom
  exact hOM (geom_counterexample_imp_OM3Counterexample (n := n) (N := N) hgeom)

/-- If there is no chirotope-level counterexample, then every `N`-point configuration
    in general position has an `n`-point convex subset. -/
theorem ESWitnessFn_of_no_OM3Counterexample {n N : ℕ}
    (hOM : ¬ OrderType.OM3Counterexample n N) : ESWitnessFn n N := by
  classical
  intro p hp
  by_contra hconv
  exact hOM (geom_counterexample_imp_OM3Counterexample (n := n) (N := N) ⟨p, hp, hconv⟩)

end
end ErdosSzekeres
