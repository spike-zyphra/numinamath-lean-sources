import Mathlib

  theorem algebra_194881 :
  {(x, y) : ℝ × ℝ | x ^ 4 + y ^ 4 = 17 ∧ x + y = 3 } = {(1, 2), (2, 1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfies the system
    rintro ⟨h1, h2⟩
    have h3 : y = 3 - x := by linarith
    rw [h3] at h1
    have h4 : x ^ 4 - 6 * x ^ 3 + 27 * x ^ 2 - 54 * x + 32 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 3 * x + 16), sq_nonneg (x - 1), sq_nonneg (x - 2)]
    have h5 : (x - 1) * (x - 2) * (x^2 - 3 * x + 16) = 0 := by
      nlinarith [h4]
    cases' (mul_eq_zero.mp h5) with h6 h7
    cases' (mul_eq_zero.mp h6) with h8 h9
    · -- Case where x - 1 = 0, so x = 1, which implies y = 2
      have hx1 : x = 1 := by linarith
      have hy1 : y = 2 := by
        linarith [show x = 1 by linarith, h3]
      left
      exact ⟨hx1, hy1⟩
    · -- Case where x - 2 = 0, so x = 2, which implies y = 1
      have hx2 : x = 2 := by linarith
      have hy2 : y = 1 := by
        linarith [show x = 2 by linarith, h3]
      right
      exact ⟨hx2, hy2⟩
    · -- Case where the quadratic factor is non-zero
      have h10 : x ^ 2 - 3 * x + 16 = 0 := by
        linarith [h7]
      nlinarith [sq_nonneg (x - 3 / 2)]
  · -- Show that both pairs satisfy the system
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (1, 2)
      constructor <;> norm_num
    · -- Check (2, 1)
      constructor <;> norm_num