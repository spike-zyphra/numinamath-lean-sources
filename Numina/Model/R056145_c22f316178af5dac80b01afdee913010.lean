import Mathlib

theorem algebra_308043 (x : ℝ) (hx : x ∈ Set.Icc 0 24) :
    (500 + 96 * x - 80 * Real.sqrt (24 * x)) ≥ 100 := by 
  rw [Set.mem_Icc] at hx
  rcases hx with ⟨hx0, hx1⟩
  have h1 : Real.sqrt (24 * x) ≥ 0 := by positivity
  nlinarith [sq_nonneg (Real.sqrt (24 * x) - 10), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 24 * x by nlinarith), 
          Real.sqrt_nonneg (24 * x), 
          mul_nonneg (show (0 : ℝ) ≤ 24 by norm_num) (show (0 : ℝ) ≤ x by linarith)]