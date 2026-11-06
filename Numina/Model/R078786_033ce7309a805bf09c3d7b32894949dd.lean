import Mathlib

theorem algebra_12023 (A B F : ℝ × ℝ)
    (hA : A.1 = 35 / 8 ∧ A.2 = 3 * Real.sqrt 15 / 8)
    (hB : B.1 = 55 / 16 ∧ B.2 = -9 * Real.sqrt 15 / 16)
    (hF : F.1 = 4 ∧ F.2 = 0)
    (hAB : A ≠ B)
    (hAF : Real.sqrt ((A.1 - F.1)^2 + (A.2 - F.2)^2) = 3 / 2) :
    Real.sqrt ((B.1 - F.1)^2 + (B.2 - F.2)^2) = 9 / 4 := by
  rcases hA with ⟨hx_A, hy_A⟩
  rcases hB with ⟨hx_B, hy_B⟩
  rcases hF with ⟨hx_F, hy_F⟩
  have h1 : (B.1 - F.1)^2 + (B.2 - F.2)^2 = (81 / 16 : ℝ) := by
    rw [hx_B, hy_B, hx_F, hy_F]
    have h15 : Real.sqrt 15 ^ 2 = 15 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    nlinarith [h15]
  have h2 : Real.sqrt ((B.1 - F.1)^2 + (B.2 - F.2)^2) = Real.sqrt (81 / 16 : ℝ) := by
    rw [h1]
  have h3 : Real.sqrt (81 / 16 : ℝ) = 9 / 4 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h2, h3]
  all_goals norm_num
  all_goals norm_num
  all_goals norm_num