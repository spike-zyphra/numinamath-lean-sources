import Mathlib

theorem algebra_222997 {x y z : ℝ} (h1 : x * (y + z) = 35) (h2 : y * (x + z) = 32) (h3 : z * (x + y) = 27) :
    (x = 5 ∧ y = 4 ∧ z = 3) ∨ (x = -5 ∧ y = -4 ∧ z = -3) := by
  have h4 : x * y + x * z + y * x + y * z + z * x + z * y = 94 := by
    nlinarith
  have h5 : x * y + y * z + z * x = 47 := by
    nlinarith [h4]
  have h6 : y * z = 12 := by
    nlinarith [h1, h5]
  have h7 : x * z = 15 := by
    nlinarith [h2, h5]
  have h8 : x * y = 20 := by
    nlinarith [h3, h5]
  have h9 : z ^ 2 = 9 := by
    nlinarith [h6, h7, h8]
  have h10 : z = 3 ∨ z = -3 := by
    have h11 : z ^ 2 - 9 = 0 := by
      linarith [h9]
    have h12 : (z - 3) * (z + 3) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h12) with
    | inl h13 =>
      left
      linarith
    | inr h14 =>
      right
      linarith
  cases h10 with
  | inl hz3 =>
    -- Case 1: z = 3, solving for y and x
    have hy4 : y = 4 := by
      rw [hz3] at h6
      nlinarith
    have hx5 : x = 5 := by
      rw [hz3] at h7
      nlinarith
    left
    constructor
    · exact hx5
    constructor
    · exact hy4
    · exact hz3
  | inr hz3 =>
    -- Case 2: z = -3, solving for y and x
    have hy4 : y = -4 := by
      rw [hz3] at h6
      nlinarith
    have hx5 : x = -5 := by
      rw [hz3] at h7
      nlinarith
    right
    constructor
    · exact hx5
    constructor
    · exact hy4
    · exact hz3