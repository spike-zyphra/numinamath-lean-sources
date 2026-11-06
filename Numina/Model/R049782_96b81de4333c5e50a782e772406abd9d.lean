import Mathlib

theorem algebra_6696 {x : ℝ} (hx : x > 0) (h : x = 9 + 1 / x) :
    x ^ 2 + 1 / x ^ 2 = 83 := by
        have h1 : x - 1 / x = 9 := by
            field_simp [(show x ≠ 0 by linarith)] at h ⊢ 
            linarith
        have h2 : (x - 1 / x) ^ 2 = 81 := by 
            rw [h1]
            norm_num
        have eq1 : (x - 1 / x) ^ 2 = x ^ 2 + 1 / x ^ 2 - 2 := by
            field_simp [(show x ≠ 0 by linarith)]
            ring
        linarith [h2, eq1]