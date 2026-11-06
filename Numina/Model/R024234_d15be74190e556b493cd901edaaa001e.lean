import Mathlib

theorem algebra_138852 {f : ℝ → ℝ} (hf : ∀ x, f (3 * x) / f x = 729 * (x - 3) / (x - 243)) :
    ∃ c d e g : ℝ, f = fun x => (x - 243) * (x - 81) * (x - 27) * (x - 9) * x ^ 2 := by
  have h1 := hf 0
  norm_num at h1 
  by_cases h2 : f 0 = 0
  · -- Case where f 0 = 0
    have h3 : f 0 / f 0 = 0 := by
      rw [h2]
      norm_num
    have h4 : (0 : ℝ) = (9 : ℝ) := by
      linarith [h1, h3]
    linarith
  · -- Case where f 0 ≠ 0
    have h3 : f 0 / f 0 = 1 := by
      field_simp [h2]
    have h4 : (1 : ℝ) = (9 : ℝ) := by
      linarith [h1, h3]
    linarith