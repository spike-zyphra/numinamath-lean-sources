import Mathlib

theorem algebra_286183 :
  { (x, y) : ℝ × ℝ | (x + y) ^ 4 = 6 * x ^ 2 * y ^ 2 - 215 ∧ x * y * (x ^ 2 + y ^ 2) = -78 } =
  { (3, -2), (-2, 3), (-3, 2), (2, -3) } := by 
  ext ⟨x, y⟩ 
  simp 
  constructor
  · -- First direction: if (x, y) is a solution, then (x, y) ∈ {(3, -2), (-2, 3), (-3, 2), (2, -3)}
    rintro ⟨h1, h2⟩ 
    have h3 : (x + y) ^ 2 = 1 := by 
      nlinarith [sq_nonneg ((x + y) ^ 2), sq_nonneg (x * y), sq_nonneg (x^2 - y^2), sq_nonneg (x - y)]
    have h4 : x + y = 1 ∨ x + y = -1 := by 
      have h5 : (x + y) ^ 2 = 1 := h3 
      have : (x + y - 1) * (x + y + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp this) with h5 h6 
      · -- Case where x + y - 1 = 0, so x + y = 1.
        left 
        linarith 
      · -- Case where x + y + 1 = 0, so x + y = -1.
        right 
        linarith 
    cases h4 with
    | inl h4l =>
      -- Assume x + y = 1
      have h5 : x * y = -6 := by 
        nlinarith [sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg ((x + y) ^ 2 - 1), h4l]
      have h6 : x = 3 ∨ x = -2 := by
        have h7 : y = 1 - x := by 
          linarith [h4l] 
        rw [h7] at h5 
        have h8 : x ^ 2 - x - 6 = 0 := by 
          nlinarith 
        have h9 : (x - 3) * (x + 2) = 0 := by
          nlinarith 
        cases' (mul_eq_zero.mp h9) with h9 h9 
        · -- Case where x - 3 = 0, so x = 3.
          left 
          linarith 
        · -- Case where x + 2 = 0, so x = -2.
          right 
          linarith 
      cases h6 with 
      | inl h8 =>
        -- Assume x = 3, prove y = -2.
        have h7 : y = -2 := by linarith [h4l, h8]
        simp [h8, h7]
      | inr h8 =>
        -- Assume x = -2, prove y = 3.
        have h7 : y = 3 := by linarith [h4l, h8]
        simp [h8, h7]
    | inr h4r =>
      -- Assume x + y = -1
      have h5 : x * y = -6 := by 
        nlinarith [sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg ((x + y) ^ 2 - 1), h4r]
      have h6 : x = 2 ∨ x = -3 := by 
        have h7 : y = -1 - x := by 
          linarith [h4r]
        rw [h7] at h5 
        have h8 : x ^ 2 + x - 6 = 0 := by 
          nlinarith 
        have h9 : (x - 2) * (x + 3) = 0 := by
          nlinarith 
        cases' (mul_eq_zero.mp h9) with h9 h9 
        · -- Case where x - 2 = 0, so x = 2.
          left 
          linarith 
        · -- Case where x + 3 = 0, so x = -3.
          right 
          linarith 
      cases h6 with
      | inl h8 =>
        -- Assume x = 2, prove y = -3.
        have h7 : y = -3 := by linarith [h4r, h8]
        simp [h8, h7]
      | inr h8 =>
        -- Assume x = -3, prove y = 2.
        have h7 : y = 2 := by linarith [h4r, h8]
        simp [h8, h7]
  · -- Now prove the reverse implication (mpr)
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- First point (3, -2)
      constructor 
      · -- First equation
        norm_num
      · -- Second equation
        norm_num
    · -- Second point (-2, 3)
      constructor 
      · -- First equation 
        norm_num 
      · -- Second equation 
        norm_num 
    · -- Third point (-3, 2)
      constructor 
      · -- First equation 
        norm_num 
      · -- Second equation 
        norm_num 
    · -- Fourth point (2, -3)
      constructor 
      · -- First equation 
        norm_num 
      · -- Second equation 
        norm_num