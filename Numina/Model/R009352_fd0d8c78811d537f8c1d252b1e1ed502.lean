import Mathlib

theorem algebra_8979 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 4 → f x = Real.sqrt x) (hf' : ∀ x, x < 4 → f x = 2 ^ x) : f (f 2) = 2 := by
  have h1 : f 2 = (4 : ℝ) := by
    specialize hf' 2 (by norm_num)
    rw [hf']
    norm_num
  have h2 : f (4 : ℝ) = (2 : ℝ) := by
    specialize hf 4 (by norm_num)
    rw [hf]
    have h3 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h3]
    all_goals norm_num
  rw [h1]
  exact h2