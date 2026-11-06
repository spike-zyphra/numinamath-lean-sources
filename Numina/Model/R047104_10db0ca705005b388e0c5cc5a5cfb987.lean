import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Definition of our quadratic function parameterized by m -/
def quadraticFunction (m : ℝ) (x : ℝ) : ℝ := x^2 + 3*x + m - 2

/- Definition for a function intersecting y-axis at a specific point -/
def intersectsYAxisAt (f : ℝ → ℝ) (y : ℝ) : Prop :=
  f 0 = y

/- Definition for a function intersecting y-axis in positive half-plane -/
def intersectsYAxisPositively (f : ℝ → ℝ) : Prop :=
  ∃ y : ℝ, y > 0 ∧ intersectsYAxisAt f y

theorem algebra_9266 (m : ℝ) :
    intersectsYAxisPositively (quadraticFunction m) ↔ m > 2 := by
  constructor
  · -- First direction: if the quadratic intersects the y-axis in the positive half-plane, then m > 2
    rintro ⟨y, hy, h⟩
    have h1 : quadraticFunction m 0 = y := h
    have eq2 : m - 2 = y := by
      have eq3 : quadraticFunction m 0 = y := h1
      simp [quadraticFunction] at eq3 ⊢
      linarith
    linarith [hy, eq2]
  · -- Second direction: if m > 2, then the quadratic intersects the y-axis in the positive half-plane
    intro hm
    use m - 2
    constructor
    · -- Show that y > 0
      linarith
    · -- Show that intersectsYAxisAt (quadraticFunction m) (m - 2)
      unfold intersectsYAxisAt
      simp [quadraticFunction]
      all_goals norm_num
      <;> linarith <;> norm_num