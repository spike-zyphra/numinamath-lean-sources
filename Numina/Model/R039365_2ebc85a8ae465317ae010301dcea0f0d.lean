import Mathlib

theorem algebra_55870 : {x : ℝ × ℝ |  x.1^3 + 3 * x.1 * x.2^2 = 49 ∧ x.1^2 + 8 * x.1 * x.2 + x.2^2 = 8 * x.2 + 17 * x.1} =
  {(1, 4), (1, -4)} := by
  ext ⟨x, y⟩
  simp
  constructor
  -- Forward: the solutions satisfy the equation system.
  .
    rintro ⟨h1, h2⟩
    -- from equation2−16 equation2 to gety^2=16
    have h3 : (x - 1)^2 = 0 := by 
      nlinarith [sq_nonneg (y^2 - 16), sq_nonneg (x - 1), sq_nonneg (y - 4), sq_nonneg (y + 4), sq_nonneg (x ^ 2 - 1), sq_nonneg ((y - 4) * (y + 4)), sq_nonneg ((x - 1) * (y ^ 2 - 16)), sq_nonneg (y ^ 2 - 16)]
    have hx1 : x = 1 := by 
      nlinarith
    rw [hx1] at h1 h2
    have hy1 : y ^ 2 = 16 := by
      nlinarith
    have hy2 : y = 4 ∨ y = -4 := by
      have h4 : (y - 4) * (y + 4) = 0 := by
        linarith [hy1]
      cases' (mul_eq_zero.mp h4) with h41 h42
      left
      linarith
      right
      linarith
    cases hy2 with
    | inl hy4 =>
      simp [hx1, hy4]
      <;> tauto
    | inr hy4 =>
      simp [hx1, hy4]
      <;> tauto
  -- Backward: the solutions satisfy the equation system s * b.
  .
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num