import Mathlib

theorem algebra_604728 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
(x ^ 2 + y * z) / (x ^ 2 + y * z + 1) + (y ^ 2 + z * x) / (y ^ 2 + z * x + 1) + (z ^ 2 + x * y) / (z ^ 2 + x * y + 1) ≤ 2 := by

    have h1 : ∀ a b c: ℝ, a > 0 → b > 0 → c > 0 → (a ^ 2 + b * c) / (a ^ 2 + b * c + 1) = 1 - 1 / (a ^ 2 + b * c + 1) := by
        intro a b c ha hb hc
        field_simp
    rw [h1 x y z hx hy hz]
    rw [h1 y z x hy hz hx]
    rw [h1 z x y hz hx hy]

    have h3 : 1 / (x ^ 2 + y * z + 1) + 1 / (y ^ 2 + z * x + 1) + 1 / (z ^ 2 + x * y + 1) ≥ 1 := by 
        have h11 : x^2 + y^2 + z^2 = 3 := h
        have h12 : x * y + y * z + z * x ≤ 3 := by 
            nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
        have h13 : 0 < (x ^ 2 + y * z + 1) * (y ^ 2 + z * x + 1) * (z ^ 2 + x * y + 1) := by positivity
        have h14 : 1 / (x ^ 2 + y * z + 1) + 1 / (y ^ 2 + z * x + 1) + 1 / (z ^ 2 + x * y + 1) - 1 ≥ 0 := by
            have h_eq : 1 / (x ^ 2 + y * z + 1) + 1 / (y ^ 2 + z * x + 1) + 1 / (z ^ 2 + x * y + 1) - 1 =
                ((y ^ 2 + z * x + 1) * (z ^ 2 + x * y + 1) + (x ^ 2 + y * z + 1) * (z ^ 2 + x * y + 1) + (x ^ 2 + y * z + 1) * (y ^ 2 + z * x + 1) - (x ^ 2 + y * z + 1) * (y ^ 2 + z * x + 1) * (z ^ 2 + x * y + 1)) / ((x ^ 2 + y * z + 1) * (y ^ 2 + z * x + 1) * (z ^ 2 + x * y + 1)) := by 
                field_simp
                ring 
            rw [h_eq]
            apply div_nonneg 
            nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
                sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
                mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
                mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
                mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith), 
                mul_pos (show 0 < z * x by nlinarith) (show 0 < x * y by nlinarith)
                ]
            all_goals positivity 
        linarith 
    have h4 : (1 - 1 / (x ^ 2 + y * z + 1)) + (1 - 1 / (y ^ 2 + z * x + 1)) + (1 - 1 / (z ^ 2 + x * y + 1)) ≤ 2 := by
        linarith
    linarith