import Mathlib

theorem algebra_220825:
    {(x, y, z) : ℝ × ℝ × ℝ | 2 * y + x - x ^ 2 - y ^ 2 = 0 ∧ z - x + y - y * (x + z) = 0 ∧ -2 * y + z - y ^ 2 - z ^ 2 = 0} = {(0, 0 ,0), (1, 0, 1)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume h
    rintro ⟨h1, h2, h3⟩
    have h4 : y = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (z - 1), sq_nonneg (y), sq_nonneg (x - z)]
    have h5 : x = 0 ∨ x = 1 := by
      rw [h4] at h1
      have : x * (x - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp this) with h6 h7
      · -- Case x = 0
        left
        linarith
      · -- Case x - 1 = 0, so x = 1
        right
        linarith
    cases h5 with
    | inl h6 =>
      -- x = 0
      have h7 : z = 0 := by
        rw [h4, h6] at h2
        nlinarith
      left
      simp [h6, h4, h7]
    | inr h7 =>
      -- x = 1
      have h8 : z = 1 := by
        rw [h4, h7] at h2
        nlinarith
      right
      simp [h7, h4, h8]
  · -- Show the reverse
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- Case (0, 0, 0)
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      · -- Third equation
        norm_num
    · -- Case (1, 0, 1)
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      · -- Third equation
        norm_num