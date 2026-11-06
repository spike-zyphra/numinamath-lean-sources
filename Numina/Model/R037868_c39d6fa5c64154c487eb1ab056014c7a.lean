import Mathlib

theorem algebra_232425 (x : ℝ) (hx : x ≠ 0) :
    2 * Real.cos (Real.pi * x) = x + 1 / x ↔ x = -1 := by
  constructor
  · -- Assume 2 * cos(pi * x) = x + 1/x, prove x = -1
    intro h
    have h1 : x + 1 / x = (x ^ 2 + 1) / x := by
      field_simp [hx]
      <;> nlinarith
    rw [h1] at h
    have h2 : -1 ≤ Real.cos (Real.pi * x) ∧ Real.cos (Real.pi * x) ≤ 1 := by
      constructor
      · -- Show -1 ≤ cos(pi * x)
        linarith [Real.neg_one_le_cos (Real.pi * x)]
      · -- Show cos(pi * x) ≤ 1
        linarith [Real.cos_le_one (Real.pi * x)]
    have h3 : -2 ≤ 2 * Real.cos (Real.pi * x) ∧ 2 * Real.cos (Real.pi * x) ≤ 2 := by
      constructor
      · linarith [h2.1]
      · linarith [h2.2]
    have h4 : -2 ≤ (x ^ 2 + 1) / x := by linarith [h, h3.1]
    have h5 : (x ^ 2 + 1) / x ≤ 2 := by linarith [h, h3.2]
    by_cases h6 : x > 0
    · -- Assume x > 0
      have h7 : (x ^ 2 + 1) / x ≤ 2 := h5
      have h8 : x ^ 2 + 1 ≤ 2 * x := by
        have h8 : (x ^ 2 + 1) / x ≤ 2 := h5
        apply (div_le_iff₀ (by linarith)).mp at h8
        nlinarith
      have h9 : (x - 1) ^ 2 ≤ 0 := by
        nlinarith
      have h10 : x - 1 = 0 := by
        nlinarith [sq_nonneg (x - 1)]
      have h11 : x = 1 := by linarith
      rw [h11] at h
      norm_num [Real.cos_pi] at h
    · -- Assume x ≤ 0
      have h7 : x < 0 := by
        by_contra h7
        push_neg at h7
        have h8 : x = 0 := by nlinarith
        contradiction
      have h8 : -2 ≤ (x ^ 2 + 1) / x := h4
      have h9 : (x ^ 2 + 1) / x ≤ 2 := h5
      have h11 : -2 * x ≥ x ^ 2 + 1 := by
        have h11 : -2 ≤ (x ^ 2 + 1) / x := h4
        apply (le_div_iff_of_neg (by linarith)).mp at h11
        nlinarith
      have h12 : (x + 1) ^ 2 ≤ 0 := by
        nlinarith
      have h13 : x + 1 = 0 := by
        nlinarith [sq_nonneg (x + 1)]
      have h14 : x = -1 := by linarith
      linarith
  · -- Assume x = -1, prove 2 * cos(pi * x) = x + 1/x
    intro h
    rw [h]
    have h1 : Real.cos (Real.pi * (-1 : ℝ)) = -1 := by
      have h1 : Real.cos (Real.pi * (-1 : ℝ)) = Real.cos (-Real.pi) := by ring
      rw [h1]
      have h2 : Real.cos (-Real.pi) = Real.cos (Real.pi) := by
        rw [show -Real.pi = - (Real.pi) by ring]
        rw [Real.cos_neg]
      rw [h2]
      have h3 : Real.cos (Real.pi) = -1 := Real.cos_pi
      linarith
    rw [h1]
    norm_num