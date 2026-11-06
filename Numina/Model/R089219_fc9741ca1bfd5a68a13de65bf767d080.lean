import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_288870 (x y : ℝ) (hx : |x| < 1) (hy : |y| < 1) (hxy : x * y ≠ 0)
  (h : ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋) :
  (x, y) ∈ {(x, y) : ℝ × ℝ | -1 < x ∧ x < 1 ∧ -1 < y ∧ y < 1 ∧ x * y ≠ 0 ∧ ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋} := by
  have hx1 : -1 < x := by
    linarith [abs_lt.mp hx]
  have hx2 : x < 1 := by 
    linarith [abs_lt.mp hx]
  have hy1 : -1 < y := by 
    linarith [abs_lt.mp hy]
  have hy2 : y < 1 := by 
    linarith [abs_lt.mp hy]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by exact hxy, by exact h⟩