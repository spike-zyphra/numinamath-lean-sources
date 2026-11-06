import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_9103 (x : ℝ) (hx : 3 < x): x = 4 ↔
∃ z : ℝ, logb 2 (x^2 - 3 * x - 2) + I * logb 2 (x - 3) = z := by
  constructor
  · -- Assume x = 4, prove that there exists a real z such that the complex expression is real
    intro hx_eq
    rw [hx_eq]
    use 1
    have h1 : logb (2 : ℝ) (4 ^ 2 - 3 * (4 : ℝ) - 2) = 1 := by
      norm_num [logb_eq_iff_rpow_eq]
    have h2 : logb (2 : ℝ) (4 - 3) = 0 := by
      norm_num [logb_eq_iff_rpow_eq]
    simp [h1, h2]
    <;> norm_num [Complex.ext_iff]
    all_goals norm_num [h1, h2]
  · -- Assume there exists a real z such that the complex expression is real, prove x = 4
    rintro ⟨z, h_eq⟩
    have h2 : logb 2 (x - 3) = 0 := by
      simpa using congr_arg Complex.im h_eq
    have hx1 : x - 3 = 1 := by
      rw [logb_eq_iff_rpow_eq] at h2
      · -- Show that x - 3 = 1
        linarith
      all_goals
        linarith
    linarith