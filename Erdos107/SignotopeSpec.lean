import Mathlib.Data.Set.Insert
import Erdos107.Bridge
import Erdos107.OrderType

namespace ErdosSzekeres

/-- Inside-triangle predicate for an abstract order type. -/
def InsideTriangle {N : ℕ} (ot : OrderType N) (a b c p : Fin N) : Prop :=
  ot.σ a b p = ot.σ a b c ∧ ot.σ b c p = ot.σ a b c ∧ ot.σ c a p = ot.σ a b c

/-- For real points, convex-hull inclusion implies the inside-triangle predicate. -/
lemma insideTriangle_of_convexHull_triangle {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) {a b c d : Fin N}
    (habc : Distinct3 a b c) (habd : Distinct3 a b d)
    (hbcd : Distinct3 b c d) (hcad : Distinct3 c a d)
    (hd : p d ∈ convexHull ℝ ({p a, p b, p c} : Set Plane)) :
    InsideTriangle (orderTypeOfPoints p hp) a b c d := by
  classical
  have h1 : decide (det3 p a b d > 0) = decide (det3 p a b c > 0) :=
    det3_same_sign_of_convexHull_triangle (p := p) (hp := hp)
      (a := a) (b := b) (c := c) (d := d) habc habd hd
  have hset_bca : ({p b, p c, p a} : Set Plane) = ({p a, p b, p c} : Set Plane) := by
    ext x
    simp [Set.insert_comm, Set.pair_comm, or_left_comm, or_assoc, or_comm]
  have hd_bca : p d ∈ convexHull ℝ ({p b, p c, p a} : Set Plane) := by
    simpa [hset_bca] using hd
  have h2 : decide (det3 p b c d > 0) = decide (det3 p b c a > 0) :=
    det3_same_sign_of_convexHull_triangle (p := p) (hp := hp)
      (a := b) (b := c) (c := a) (d := d)
      (by
        rcases habc with ⟨hab, hac, hbc⟩
        exact ⟨hbc, by simpa [eq_comm] using hab, by simpa [eq_comm] using hac⟩)
      hbcd hd_bca
  have hset_cab : ({p c, p a, p b} : Set Plane) = ({p a, p b, p c} : Set Plane) := by
    ext x
    simp [Set.insert_comm, Set.pair_comm, or_left_comm, or_assoc, or_comm]
  have hd_cab : p d ∈ convexHull ℝ ({p c, p a, p b} : Set Plane) := by
    simpa [hset_cab] using hd
  have h3 : decide (det3 p c a d > 0) = decide (det3 p c a b > 0) :=
    det3_same_sign_of_convexHull_triangle (p := p) (hp := hp)
      (a := c) (b := a) (c := b) (d := d)
      (by
        rcases habc with ⟨hab, hac, hbc⟩
        exact ⟨by simpa [eq_comm] using hac, by simpa [eq_comm] using hbc, hab⟩)
      hcad hd_cab
  refine ⟨?_, ?_, ?_⟩
  · simpa [orderTypeOfPoints] using h1
  · -- align `b,c,a` with the `(a,b,c)` orientation
    have h2' : decide (det3 p b c a > 0) = decide (det3 p a b c > 0) := by
      simpa [det3_cycle (p := p) a b c]
    have h2'' : decide (det3 p b c d > 0) = decide (det3 p a b c > 0) := by
      simpa [h2'] using h2
    simpa [orderTypeOfPoints] using h2''
  · have h3' : decide (det3 p c a b > 0) = decide (det3 p a b c > 0) := by
      simpa [det3_cycle (p := p) c a b]
    have h3'' : decide (det3 p c a d > 0) = decide (det3 p a b c > 0) := by
      simpa [h3'] using h3
    simpa [orderTypeOfPoints] using h3''

/-- Index order agrees with increasing x-coordinate. -/
def XOrdered {N : ℕ} (p : Fin N → Plane) : Prop :=
  ∀ {i j : Fin N}, i < j → p i 0 < p j 0

/-- Signotope axioms (CNF form) for every increasing 4-tuple. -/
def SignotopeAxioms {N : ℕ} (ot : OrderType N) : Prop :=
  ∀ a b c d : Fin N, a < b → b < c → c < d →
    ((ot.σ a b c = false) ∨ (ot.σ a b d = true) ∨ (ot.σ a c d = false) ∨ (ot.σ b c d = true)) ∧
    ((ot.σ a b c = true) ∨ (ot.σ a b d = false) ∨ (ot.σ a c d = true) ∨ (ot.σ b c d = false))

/-- CC-system interiority axiom. -/
def CCInteriority {N : ℕ} (ot : OrderType N) : Prop :=
  ∀ p q r t : Fin N, Distinct4 p q r t →
    ot.σ t q r = true → ot.σ p t r = true → ot.σ p q t = true → ot.σ p q r = true

/-- Pairwise distinctness for a 5-tuple. -/
def Distinct5 {N : ℕ} (a b c d e : Fin N) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
  b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
  c ≠ d ∧ c ≠ e ∧ d ≠ e

/-- CC-system transitivity axiom. -/
def CCTransitivity {N : ℕ} (ot : OrderType N) : Prop :=
  ∀ t s p q r : Fin N, Distinct5 t s p q r →
    ot.σ t s p = true → ot.σ t s q = true → ot.σ t s r = true →
    ot.σ t p q = true → ot.σ t q r = true → ot.σ t p r = true

/-- Full CC-system: interiority + transitivity. -/
def CCSystem {N : ℕ} (ot : OrderType N) : Prop :=
  CCInteriority ot ∧ CCTransitivity ot

/-- For real points in general position and x-order, the induced order type is a signotope. -/
axiom orderTypeOfPoints_signotope {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) (hx : XOrdered p) :
    SignotopeAxioms (orderTypeOfPoints p hp)

/-- For real points in general position, the induced order type satisfies CC-system axioms. -/
axiom orderTypeOfPoints_ccSystem {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) : CCSystem (orderTypeOfPoints p hp)

/-- No-convex-6-gon condition in inside-triangle form (for a fixed order type). -/
def No6GonClause {N : ℕ} (ot : OrderType N) : Prop :=
  ∀ f : Fin 6 ↪ Fin N,
    ∃ i a b c : Fin 6, Distinct4 i a b c ∧
      InsideTriangle ot (f a) (f b) (f c) (f i)

/-- Soundness bridge (geometric): no convex 6-gon implies inside-triangle clauses. -/
axiom noConvex6_imp_No6GonClause {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) :
    (¬ HasConvexSubset (n := 6) p) → No6GonClause (orderTypeOfPoints p hp)


end ErdosSzekeres
