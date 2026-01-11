import Erdos107.ErdosSzekeres
import Erdos107.OrderType

namespace ErdosSzekeres

noncomputable section

/-- The (abstract) order type induced by a labelled point configuration in general position. -/
def orderTypeOfPoints {N : ℕ} (p : Fin N → Plane) (hp : GeneralPositionFn p) :
    ErdosSzekeres.OrderType N := by
  classical
  -- TODO: define `σ` using the orientation of triples (e.g. sign of a 2×2 determinant).
  sorry

/-- The induced order type satisfies the rank-3 chirotope (Grassmann–Plücker) axiom scheme. -/
theorem orderTypeOfPoints_isChirotope {N : ℕ} (p : Fin N → Plane) (hp : GeneralPositionFn p) :
    OrderType.IsChirotope (orderTypeOfPoints p hp) := by
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
