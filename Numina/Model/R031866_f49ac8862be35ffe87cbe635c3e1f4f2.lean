import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_279857 (p a : ℝ) (hp : p > 0) (ha : a > 0) :
  IsGreatest {A : ℝ | ∃ (x y : ℝ), y^2 = 2 * p * x ∧ 0 ≤ x ∧ x ≤ a ∧ 0 ≤ y ∧ A = 2 * y * (a - x)} (4 * a / 3 * Real.sqrt (2 * a * p / 3)) := by
  constructor
  · -- Show that the area is achievable.
    use a / 3
    use Real.sqrt (2 * a * p / 3)
    constructor
    · -- Show that y^2 = 2 * p * x
      have h1 : (Real.sqrt (2 * a * p / 3)) ^ 2 = 2 * a * p / 3 := by
        apply Real.sq_sqrt
        positivity
      nlinarith
    constructor
    · -- Show that 0 ≤ x
      linarith [show 0 ≤ a by positivity]
    constructor
    · -- Show that x ≤ a
      linarith [show a > 0 by linarith [ha]]
    constructor
    · -- Show that 0 ≤ y
      positivity
    · -- Verify the area
      have h1 : Real.sqrt (2 * a * p / 3) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (2 * a * p / 3), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * a * p / 3) by positivity)]
  · -- Show that the area is greatest.
    intro A hA
    rcases hA with ⟨x, y, h_eq, hx1, hx2, hy1, hA_eq⟩
    nlinarith [sq_nonneg (y - Real.sqrt (2 * a * p / 3)), sq_nonneg (x - a / 3), Real.sqrt_nonneg (2 * a * p / 3), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * a * p / 3 by positivity), sq_nonneg (y ^ 2 - 2 * p * x), sq_nonneg ((a - x) - 2 * a / 3), mul_nonneg (Real.sqrt_nonneg (2 * a * p / 3)) (Real.sqrt_nonneg (2 * a * p / 3)), mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ a - x by nlinarith), mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ a - x by nlinarith)]