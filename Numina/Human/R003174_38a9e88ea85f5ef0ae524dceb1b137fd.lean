import Mathlib

theorem algebra_159261 (a : ℝ) (ha : a = 27.56) (n : ℕ) (hn : n = 100) (σ : ℝ)
    (hσ : σ = 5.2) :
    (a - 26) / (σ / √n) > 1.96 := by
        rw [ha, hn, hσ]
        have h1 : (27.56 : ℝ) - 26 = 1.56 := by norm_num
        have h2 : (5.2 : ℝ) / √(100 : ℕ) = 0.52 := by
            have hsqrt : √(100 : ℕ) = (10 : ℝ) := by
                rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            rw [hsqrt]
            norm_num
        rw [h1, h2]
        norm_num [Real.sqrt_eq_iff_sq_eq]