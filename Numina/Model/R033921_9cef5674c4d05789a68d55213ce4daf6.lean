import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_200144 (x y : ℝ) (hx : x ∈ Ioo (-2) 2) (hy : y ∈ Ioo (-2) 2)
  (hxy : x * y = -1) :
  4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) ≥ 12 / 5 := by 
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    have hx3 : 4 - x^2 > 0 := by
      nlinarith
    have hy3 : 9 - y^2 > 0 := by
      nlinarith
    have h1 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5 ≥ 0 := by
      have hx4 : 0 < (4 - x^2) := hx3
      have hy4 : 0 < (9 - y^2) := hy3
      have hx5 : 0 < (4 - x^2) * (9 - y^2) := by 
        positivity
      have h2 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5 =
          (4 * 5 * (9 - y ^ 2) + 9 * 5 * (4 - x^2) - 12 * (4 - x^2) * (9 - y^2)) / (5 * (4 - x^2) * (9 - y^2)) := by 
        field_simp 
        <;> ring 
      rw [h2] at *
      have hx6 : (4 * 5 * (9 - y ^ 2) + 9 * 5 * (4 - x^2) - 12 * (4 - x^2) * (9 - y^2)) ≥ 0 := by 
        have h3 : x^2 * y^2 = 1 := by 
          have : x * y = -1 := hxy 
          have : (x * y) ^2 = 1 := by 
            rw [this] 
            norm_num 
          nlinarith 
        nlinarith [ sq_nonneg (x^2 - 2/3), sq_nonneg (y^2 - 2/3), sq_nonneg (x^2 * y^2 - 1), sq_nonneg (x * y), mul_pos hx3 hy3, mul_pos hx3 (show 0 < 9 - y ^ 2 by nlinarith), mul_pos (show 0 < 4 - x ^ 2 by nlinarith) hy3 
          ]
      have hx7 : (5 * (4 - x^2) * (9 - y^2)) > 0 := by 
        positivity 
      apply div_nonneg 
      linarith 
      all_goals nlinarith 
    linarith