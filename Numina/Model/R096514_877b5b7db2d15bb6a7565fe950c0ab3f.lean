import Mathlib

open Real

theorem algebra_222575 {A : ℝ}
    (hA : A = (sqrt 2022 + 1) / (sqrt 2022 - 1) - 2 / (sqrt 2022 + 1)) :
    sqrt (1 - A ^ (-1 : ℤ)) = 2 / 45 := by
  have h1 : A = 2025 / 2021 := by
    rw [hA]
    -- Let's compute both terms and simplify
    have h2 : sqrt 2022 > 0 := by positivity
    have h3 : sqrt 2022 ^ 2 = 2022 := Real.sq_sqrt (by norm_num)
    have h4 : sqrt 2022 - 1 ≠ 0 := by
      have h5 : sqrt 2022 > 1 := by
        have h6 : sqrt 2022 > sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have h7 : sqrt 1 = (1 : ℝ) := Real.sqrt_one
        linarith [h6, h7]
      linarith
    have h8 : sqrt 2022 + 1 ≠ 0 := by
      have h9 : sqrt 2022 > 0 := by positivity
      linarith
    field_simp [h4, h8, h3]
    <;> ring_nf <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2022 : ℝ) by norm_num), h3]
  have hA1 : 1 - A ^ (-1 : ℤ) = 4 / 2025 := by
    rw [h1]
    norm_num
  rw [hA1]
  rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num