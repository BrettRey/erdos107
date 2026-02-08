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

/-- Plücker relation for the 2D determinant. -/
lemma det2_plucker (u v w z : Plane) :
    det2 u v * det2 w z - det2 u w * det2 v z + det2 u z * det2 v w = 0 := by
  simp [det2]
  ring

/-- Plücker relation for `det3` (rank-2 minors). -/
lemma det3_plucker {N : ℕ} (p : Fin N → Plane) (a b c d e : Fin N) :
    det3 p a b c * det3 p a d e - det3 p a b d * det3 p a c e
      + det3 p a b e * det3 p a c d = 0 := by
  simpa [det3] using
    (det2_plucker (p b - p a) (p c - p a) (p d - p a) (p e - p a))

/-- Oriented area decomposition for a triangle and a point. -/
lemma det3_sum {N : ℕ} (p : Fin N → Plane) (a b c d : Fin N) :
    det3 p a b d + det3 p b c d + det3 p c a d = det3 p a b c := by
  simp [det3, det2]
  ring

/-- `signMul` matches sign of the product for nonzero reals. -/
lemma signMul_decide_pos_eq (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    OrderType.signMul (decide (x > 0)) (decide (y > 0)) = decide (x * y > 0) := by
  classical
  by_cases hxpos : x > 0
  · by_cases hypos : y > 0
    · have hxy : x * y > 0 := mul_pos hxpos hypos
      simp [OrderType.signMul, hxpos, hypos, hxy]
    · have hyneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hy
      have hxy' : ¬ x * y > 0 := by
        have hxy : x * y < 0 := mul_neg_of_pos_of_neg hxpos hyneg
        linarith
      simp [OrderType.signMul, hxpos, hypos, hxy']
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    by_cases hypos : y > 0
    · have hxy' : ¬ x * y > 0 := by
        have hxy : x * y < 0 := mul_neg_of_neg_of_pos hxneg hypos
        linarith
      simp [OrderType.signMul, hxpos, hypos, hxy']
    · have hyneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hy
      have hxy : x * y > 0 := mul_pos_of_neg_of_neg hxneg hyneg
      simp [OrderType.signMul, hxpos, hypos, hxy]

/-- If nonzero reals sum to zero, their signs are not all equal. -/
lemma not_all_same_sign_of_sum_zero {X Y Z : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0) (hZ : Z ≠ 0)
    (hsum : X + Y + Z = 0) :
    ¬ (decide (X > 0) = decide (Y > 0) ∧ decide (Y > 0) = decide (Z > 0)) := by
  classical
  by_cases hXpos : X > 0
  · by_cases hYpos : Y > 0
    · by_cases hZpos : Z > 0
      · have : X + Y + Z > 0 := by linarith
        linarith [hsum, this]
      · simp [hXpos, hYpos, hZpos]
    · simp [hXpos, hYpos]
  · by_cases hYpos : Y > 0
    · simp [hXpos, hYpos]
    · by_cases hZpos : Z > 0
      · simp [hXpos, hYpos, hZpos]
      · have hXlt : X < 0 := lt_of_le_of_ne (le_of_not_gt hXpos) hX
        have hYlt : Y < 0 := lt_of_le_of_ne (le_of_not_gt hYpos) hY
        have hZlt : Z < 0 := lt_of_le_of_ne (le_of_not_gt hZpos) hZ
        have : X + Y + Z < 0 := by linarith
        linarith [hsum, this]

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
  classical
  -- Reduce to linear independence of the two difference vectors.
  let p' : Fin 3 → Plane := ![p i, p j, p k]
  have hAff : AffineIndependent ℝ p' :=
    hp i j k hijk.1 hijk.2.1 hijk.2.2
  have hlin_sub :
      LinearIndependent ℝ (fun t : {x : Fin 3 // x ≠ (0 : Fin 3)} => (p' t -ᵥ p' 0)) :=
    (affineIndependent_iff_linearIndependent_vsub (k := ℝ) p' (0 : Fin 3)).1 hAff

  -- Injective map from `Fin 2` into the subtype `{x : Fin 3 // x ≠ 0}`.
  let g : Fin 2 → {x : Fin 3 // x ≠ (0 : Fin 3)} := fun t => ⟨Fin.succ t, by simp⟩
  have hg : Function.Injective g := by
    intro a b h
    have : (Fin.succ a : Fin 3) = Fin.succ b := by
      simpa [g] using congrArg Subtype.val h
    exact Fin.succ_inj.mp this

  have hlin :
      LinearIndependent ℝ ![p j - p i, p k - p i] := by
    have hlin' :
        LinearIndependent ℝ (fun t : Fin 2 => (p' (g t) -ᵥ p' 0)) :=
      LinearIndependent.comp hlin_sub g hg
    have hlin'' :
        LinearIndependent ℝ (fun t : Fin 2 => (p' (g t) - p' 0)) := by
      simpa [vsub_eq_sub] using hlin'
    -- Identify the two vectors.
    have hfun :
        (fun t : Fin 2 => (p' (g t) - p' 0)) =
          ![p j - p i, p k - p i] := by
      ext t <;> fin_cases t <;> simp [p', g]
    simpa [hfun] using hlin''

  -- Now show the determinant is nonzero; otherwise the two vectors are dependent.
  intro hdet
  set u : Plane := p j - p i
  set v : Plane := p k - p i
  have hdet' : det2 u v = 0 := by
    simpa [det3, u, v] using hdet

  by_cases h0 : u 0 = 0 ∧ v 0 = 0
  · -- Use the second coordinate if the first is zero.
    have hcomb : (v 1) • u + (-u 1) • v = 0 := by
      ext d; fin_cases d
      · simp [u, v, h0.1, h0.2]
      · simp [u, v]
        ring_nf
    have hz : v 1 = 0 ∧ -u 1 = 0 :=
      hlin.eq_zero_of_pair hcomb
    have hune : u ≠ 0 := by
      simpa [u] using hlin.ne_zero (i := (0 : Fin 2))
    have hu1 : u 1 = 0 := by linarith [hz.2]
    -- If both second coordinates are zero, then u=v=0, contradicting linear independence.
    have : u = 0 := by
      ext d; fin_cases d <;> simp [u, h0.1, hu1]
    exact hune this
  · -- First coordinate not both zero; use coefficients from det=0.
    have hcomb : (v 0) • u + (-u 0) • v = 0 := by
      ext d; fin_cases d
      · simp [u, v]
        ring_nf
      · have hdet'' : u 0 * v 1 - u 1 * v 0 = 0 := by
          simpa [det2] using hdet'
        have hdet''' : v 0 * u 1 - u 0 * v 1 = 0 := by
          calc
            v 0 * u 1 - u 0 * v 1 = -(u 0 * v 1 - u 1 * v 0) := by ring_nf
            _ = 0 := by simpa [hdet'']
        -- v0*u1 - u0*v1 = 0
        simpa [sub_eq_add_neg] using hdet'''
    have hz : v 0 = 0 ∧ -u 0 = 0 :=
      hlin.eq_zero_of_pair hcomb
    have hu0 : u 0 = 0 := by linarith [hz.2]
    have hv0 : v 0 = 0 := hz.1
    exact h0 ⟨hu0, hv0⟩


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
  intro a b c d e habc hade habd hace habe hacd
  -- Shorthand determinants (all nonzero by general position).
  set x1 := det3 p a b c
  set x2 := det3 p a b d
  set x3 := det3 p a b e
  set x4 := det3 p a c d
  set x5 := det3 p a c e
  set x6 := det3 p a d e
  have hx1 : x1 ≠ 0 := det3_ne_zero_of_generalPositionFn (p := p) hp (i := a) (j := b) (k := c) habc
  have hx2 : x2 ≠ 0 := det3_ne_zero_of_generalPositionFn (p := p) hp (i := a) (j := b) (k := d) habd
  have hx3 : x3 ≠ 0 := det3_ne_zero_of_generalPositionFn (p := p) hp (i := a) (j := b) (k := e) habe
  have hx4 : x4 ≠ 0 := det3_ne_zero_of_generalPositionFn (p := p) hp (i := a) (j := c) (k := d) hacd
  have hx5 : x5 ≠ 0 := det3_ne_zero_of_generalPositionFn (p := p) hp (i := a) (j := c) (k := e) hace
  have hx6 : x6 ≠ 0 := det3_ne_zero_of_generalPositionFn (p := p) hp (i := a) (j := d) (k := e) hade
  have hpl : x1 * x6 - x2 * x5 + x3 * x4 = 0 := by
    simpa [x1, x2, x3, x4, x5, x6] using det3_plucker (p := p) a b c d e
  set X := x1 * x6
  set Y := -(x2 * x5)
  set Z := x3 * x4
  have hXne : X ≠ 0 := mul_ne_zero hx1 hx6
  have hYne : Y ≠ 0 := by
    have : x2 * x5 ≠ 0 := mul_ne_zero hx2 hx5
    exact neg_ne_zero.mpr this
  have hZne : Z ≠ 0 := mul_ne_zero hx3 hx4
  have hsum : X + Y + Z = 0 := by
    have hpl' : x1 * x6 + -(x2 * x5) + x3 * x4 = 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hpl
    simpa [X, Y, Z] using hpl'
  have hgp : ¬ (decide (X > 0) = decide (Y > 0) ∧ decide (Y > 0) = decide (Z > 0)) :=
    not_all_same_sign_of_sum_zero hXne hYne hZne hsum
  have hp1 : OrderType.signMul (decide (x1 > 0)) (decide (x6 > 0)) = decide (X > 0) := by
    simpa [X] using signMul_decide_pos_eq x1 x6 hx1 hx6
  have hp3 : OrderType.signMul (decide (x3 > 0)) (decide (x4 > 0)) = decide (Z > 0) := by
    simpa [Z] using signMul_decide_pos_eq x3 x4 hx3 hx4
  have hp2 : (! OrderType.signMul (decide (x2 > 0)) (decide (x5 > 0))) = decide (Y > 0) := by
    have hmul : OrderType.signMul (decide (x2 > 0)) (decide (x5 > 0)) = decide (x2 * x5 > 0) := by
      simpa using signMul_decide_pos_eq x2 x5 hx2 hx5
    by_cases hpos : x2 * x5 > 0
    · have hYneg : ¬ (Y > 0) := by linarith [hpos]
      simp [hmul, hpos, Y, hYneg]
    · have hneg : x2 * x5 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (mul_ne_zero hx2 hx5)
      have hYpos : Y > 0 := by linarith [hneg]
      simp [hmul, hpos, Y, hYpos]
  have hgp' :
      ¬ (OrderType.signMul (decide (x1 > 0)) (decide (x6 > 0)) =
          (! OrderType.signMul (decide (x2 > 0)) (decide (x5 > 0))) ∧
          (! OrderType.signMul (decide (x2 > 0)) (decide (x5 > 0))) =
            OrderType.signMul (decide (x3 > 0)) (decide (x4 > 0))) := by
    intro hbad
    have hbad1 : decide (X > 0) = decide (Y > 0) := by
      calc
        decide (X > 0) = OrderType.signMul (decide (x1 > 0)) (decide (x6 > 0)) := by
          exact hp1.symm
        _ = (! OrderType.signMul (decide (x2 > 0)) (decide (x5 > 0))) := hbad.1
        _ = decide (Y > 0) := by
          exact hp2
    have hbad2 : decide (Y > 0) = decide (Z > 0) := by
      calc
        decide (Y > 0) = (! OrderType.signMul (decide (x2 > 0)) (decide (x5 > 0))) := by
          exact hp2.symm
        _ = OrderType.signMul (decide (x3 > 0)) (decide (x4 > 0)) := hbad.2
        _ = decide (Z > 0) := by
          exact hp3
    exact hgp ⟨hbad1, hbad2⟩
  -- Conclude GPRel by rewriting into sign comparisons.
  simpa [OrderType.GPRel, OrderType.signMul, orderTypeOfPoints, x1, x2, x3, x4, x5, x6] using hgp'

/-- The induced order type is acyclic (realizable case). -/
theorem orderTypeOfPoints_acyclic {N : ℕ} (p : Fin N → Plane) (hp : GeneralPositionFn p) :
    OrderType.Acyclic (orderTypeOfPoints p hp) := by
  classical
  intro a b c d habcd
  by_cases hpos : det3 p a b c > 0
  · -- If `d` is to the left of any edge, we are done.
    by_cases h1 : det3 p d b c > 0
    · right; left; simpa [orderTypeOfPoints, h1]
    by_cases h2 : det3 p a d c > 0
    · right; right; left; simpa [orderTypeOfPoints, h2]
    by_cases h3 : det3 p a b d > 0
    · right; right; right; simpa [orderTypeOfPoints, h3]

    -- Otherwise all three are nonpositive; contradict area decomposition.
    have h1le : det3 p d b c ≤ 0 := le_of_not_gt h1
    have h2le : det3 p a d c ≤ 0 := le_of_not_gt h2
    have h3le : det3 p a b d ≤ 0 := le_of_not_gt h3

    have h1le' : det3 p b c d ≤ 0 := by
      simpa [det3_cycle (p := p) d b c] using h1le

    have h2le' : det3 p c a d ≤ 0 := by
      have h2le1 : det3 p d c a ≤ 0 := by
        simpa [det3_cycle (p := p) a d c] using h2le
      simpa [det3_cycle (p := p) d c a] using h2le1

    have hsum : det3 p a b d + det3 p b c d + det3 p c a d = det3 p a b c :=
      det3_sum (p := p) a b c d

    have hsumle : det3 p a b d + det3 p b c d + det3 p c a d ≤ 0 := by
      linarith [h1le', h2le', h3le]

    have hle : det3 p a b c ≤ 0 := by
      linarith [hsum, hsumle]
    exact (False.elim (not_le_of_gt hpos hle))
  · left
    simp [orderTypeOfPoints, hpos]

/-- If `p` has an `n`-point convex subset, then the induced order type contains an alternating
    `n`-subset. -/
axiom convexSubset_imp_containsAlternating_axiom {n N : ℕ} {p : Fin N → Plane}
    (hp : GeneralPositionFn p) :
    HasConvexSubset (n := n) p →
      OrderType.ContainsAlternating (orderTypeOfPoints p hp) n

theorem convexSubset_imp_containsAlternating {n N : ℕ} {p : Fin N → Plane}
    (hp : GeneralPositionFn p) :
    HasConvexSubset (n := n) p →
      OrderType.ContainsAlternating (orderTypeOfPoints p hp) n := by
  classical
  exact convexSubset_imp_containsAlternating_axiom (p := p) (hp := hp)

/-- Conversely: if the induced order type contains an alternating `n`-subset, then `p` has an
    `n`-point convex subset. (This is the geometric content you’ll eventually want.) -/
axiom containsAlternating_imp_convexSubset_axiom {n N : ℕ} {p : Fin N → Plane}
    (hp : GeneralPositionFn p) :
    OrderType.ContainsAlternating (orderTypeOfPoints p hp) n →
      HasConvexSubset (n := n) p

theorem containsAlternating_imp_convexSubset {n N : ℕ} {p : Fin N → Plane}
    (hp : GeneralPositionFn p) :
    OrderType.ContainsAlternating (orderTypeOfPoints p hp) n →
      HasConvexSubset (n := n) p := by
  classical
  exact containsAlternating_imp_convexSubset_axiom (p := p) (hp := hp)

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
