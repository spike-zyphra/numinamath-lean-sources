import Mathlib

theorem inequalities_601697 (a : ℝ) (ha : a > 0) :
    (∀ x y : ℝ, x > 0 → y > 0 → (x + y) * (1 / x + a / y) ≥ 9) ↔ a ≥ 4 := by
  constructor
  · -- Forward: if inequality holds for all x > 0, y > 0 then a ≥ 4
    intro h
    have h1 := h 1 2 (by norm_num) (by norm_num)
    norm_num at h1
    nlinarith
  · -- Backward: if a ≥ 4 then inequality holds
    intro ha x y hx hy
    have h1 : (x + y) * (1 / x + a / y) = 1 + a + y / x + a * (x / y) := by
      field_simp
      <;> ring
    rw [h1]
    have h2 : y / x + a * (x / y) ≥ 4 := by
      have h3 : y / x + a * (x / y) - 4 ≥ 0 := by
        have h4 : y / x + a * (x / y) - 4 = (y ^ 2 + a * x ^ 2 - 4 * x * y) / (x * y) := by
          field_simp
          ring
        rw [h4]
        have h5 : y ^ 2 + a * x ^ 2 - 4 * x * y ≥ 0 := by
          nlinarith [sq_nonneg (y - 2 * x), sq_nonneg (x * 2 - y ), sq_nonneg (x - y ), sq_nonneg (x * (y ) ), sq_nonneg (x * 2 ), sq_nonneg (x * y - x * 2), sq_nonneg (y - 2 ), sq_nonneg (x * (y ) ), sq_nonneg (a - 4 ), sq_nonneg (x * y / 1 ), 
                      mul_pos hx (show 0 < y by linarith ), 
                      mul_pos hx (show 0 < a by linarith ), 
                      mul_pos (show 0 < y by linarith ) (show 0 < a by linarith )
                    ]
        have h6 : x * y > 0 := mul_pos hx hy
        have h7 : (x * y) > 0 := h6
        apply div_nonneg
        linarith
        all_goals nlinarith
      linarith
    nlinarith [sq_nonneg (x - y / 2 ), sq_nonneg (y - 2 * x ), 
          mul_pos hx (show 0 < x by linarith ), 
          mul_pos hx (show 0 < y by linarith ), 
          mul_pos (show 0 < y by linarith ) (show 0 < x by linarith ), 
          sq_nonneg (a - 4 ), sq_nonneg (x * y ), 
          mul_pos hx (show 0 < a by linarith ), 
          mul_pos (show 0 < y by linarith ) (show 0 < a by linarith )
        ]