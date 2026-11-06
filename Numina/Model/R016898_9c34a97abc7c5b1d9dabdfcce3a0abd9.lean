import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem inequalities_144927 (a b c : ℝ) (h : ∀ x : ℝ, |x| ≤ |1| → |a * x^2 + b * x + c| ≤ 1) :
    ∀ x : ℝ, |x| ≤ 1 → |2 * a * x + b| ≤ 4 := by
  intro x hx
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h (0 : ℝ) (by norm_num)
  have h4 := h x (show |x| ≤ |1| by simpa using hx)
  have hx' : -1 ≤ x := by linarith [abs_le.mp hx]
  have hx'' : x ≤ 1 := by linarith [abs_le.mp hx]
  have h1' : -1 ≤ a + b + c := by linarith [abs_le.mp h1]
  have h1'' : a + b + c ≤ 1 := by linarith [abs_le.mp h1]
  have h2' : -1 ≤ a - b + c := by linarith [abs_le.mp h2]
  have h2'' : a - b + c ≤ 1 := by linarith [abs_le.mp h2]
  have h3' : -1 ≤ c := by linarith [abs_le.mp h3]
  have h3'' : c ≤ 1 := by linarith [abs_le.mp h3]
  have h4' : -1 ≤ a * x^2 + b * x + c := by linarith [abs_le.mp h4]
  have h4'' : a * x^2 + b * x + c ≤ 1 := by linarith [abs_le.mp h4]
  apply abs_le.mpr
  constructor
  · -- Prove lower bound: -4 ≤ 2 * a * x + b
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (a * (x^2 - 1)), sq_nonneg ((x) * b), sq_nonneg ((x)^2 * a), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (by linarith : (0 : ℝ) ≤ 1 + x)]
  · -- Prove upper bound: 2 * a * x + b ≤ 4
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x), sq_nonneg (a * (x^2 - 1)), sq_nonneg ((x) * b), sq_nonneg ((x)^2 * a), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (by linarith : (0 : ℝ) ≤ 1 + x)]