import Mathlib

theorem algebra_302434 (x : ℝ) (hx : x ≠ 0) : 16 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) = 16 * x + 1 / x ↔ x = 1 / 4 ∨ x = -1 / 4 := by
  constructor
  · -- Assume 16 * sin(pi * x) * cos(pi * x) = 16 * x + 1 / x, prove x = 1/4 ∨ x = -1/4
    intro h_eq
    have h1 : 16 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) = 8 * (2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x)) := by ring
    rw [h1] at h_eq
    have h2 : 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) = Real.sin (2 * Real.pi * x) := by
      have hsin : Real.sin (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := by
        rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
        rw [Real.sin_two_mul]
      linarith
    rw [h2] at h_eq
    have h3 : -1 ≤ Real.sin (2 * Real.pi * x) := by
      apply Real.neg_one_le_sin
    have h4 : Real.sin (2 * Real.pi * x) ≤ 1 := by
      apply Real.sin_le_one
    have h5 : -8 ≤ 8 * Real.sin (2 * Real.pi * x) := by
      nlinarith [h3]
    have h6 : 8 * Real.sin (2 * Real.pi * x) ≤ 8 := by
      nlinarith [h4]
    have eq1 : 16 * x + 1 / x = 8 * Real.sin (2 * Real.pi * x) := by
      linarith
    have eq2 : -8 ≤ 16 * x + 1 / x := by
      nlinarith [h5, eq1]
    have eq3 : 16 * x + 1 / x ≤ 8 := by
      nlinarith [h6, eq1]
    by_cases h : x > 0
    · -- x > 0
      have h4 : (4 * x - 1) ^ 2 ≤ 0 := by
        have h5 : (16 * x + 1 / x) ≤ 8 := by
          linarith [eq3]
        have h6 : 16 * x ^ 2 + 1 ≤ 8 * x := by
          have h7 : x > 0 := h
          have h8 : 16 * x + 1 / x = (16 * x^2 + 1) / x := by
            field_simp [hx]
            <;> ring
          rw [h8] at h5
          have h9 : (16 * x ^ 2 + 1) / x ≤ (8) := by linarith [h5]
          have h10 : 16 * x ^ 2 + 1 ≤ 8 * x := by
            apply (div_le_iff₀ (by linarith)).mp at h9
            nlinarith
          linarith
        nlinarith
      have h5 : (4 * x - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (4 * x - 1)]
      have h6 : 4 * x - 1 = 0 := by
        nlinarith
      have hx1 : x = 1 / 4 := by
        nlinarith
      left
      exact hx1
    · -- not x >0
      have h7 : x ≤ 0 := by linarith
      have h8 : x < 0 := by
        by_contra h9
        push_neg at h9
        have : x = 0 := by linarith
        contradiction
      have h4 : (4 * x + 1) ^ 2 ≤ 0 := by
        have h5 : -8 ≤ 16 * x + 1 / x := by
          linarith [eq2]
        have h6 : -8 * x ≥ 16 * x ^ 2 + 1 := by
          have h7 : x < 0 := h8
          have h8 : 16 * x + 1 / x = (16 * x^2 + 1) / x := by
            field_simp [hx]
            <;> ring
          rw [h8] at h5
          have h9 : (16 * x ^ 2 + 1) / x ≥ -8 := by
            linarith [h5]
          have h10 : 16 * x ^ 2 + 1 ≤ -8 * x := by
            apply (le_div_iff_of_neg' (by linarith)).mp at h9
            nlinarith
          linarith
        nlinarith
      have h5 : (4 * x + 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (4 * x + 1)]
      have h6 : 4 * x + 1 = 0 := by
        nlinarith
      have hx1 : x = -1 / 4 := by
        nlinarith
      right
      exact hx1
  · -- Assume x = 1/4 ∨ x = -1/4, prove 16 * sin(pi * x) * cos(pi * x) = 16 * x + 1 / x
    rintro (h_eq | h_eq)
    · -- x = 1/4
      rw [h_eq]
      have h1 : Real.sin (Real.pi * (1 / 4 : ℝ)) = Real.sqrt 2 / 2 := by
        have h1 : Real.sin (Real.pi * (1 / 4 : ℝ)) = Real.sin (Real.pi / 4) := by
          ring_nf
        rw [h1]
        rw [Real.sin_pi_div_four]
      have h2 : Real.cos (Real.pi * (1 / 4 : ℝ)) = Real.sqrt 2 / 2 := by
        have h2 : Real.cos (Real.pi * (1 / 4 : ℝ)) = Real.cos (Real.pi / 4) := by
          ring_nf
        rw [h2]
        rw [Real.cos_pi_div_four]
      rw [h1, h2]
      field_simp
      <;> ring_nf <;> norm_num
    · -- x = -1/4
      rw [h_eq]
      have h1 : Real.sin (Real.pi * (-1 / 4 : ℝ)) = -Real.sqrt 2 / 2 := by
        have h1 : Real.sin (Real.pi * (-1 / 4 : ℝ)) = Real.sin (- (Real.pi / 4)) := by
          ring_nf
        rw [h1]
        rw [Real.sin_neg]
        rw [Real.sin_pi_div_four]
        all_goals ring_nf
      have h2 : Real.cos (Real.pi * (-1 / 4 : ℝ)) = Real.sqrt 2 / 2 := by
        have h2 : Real.cos (Real.pi * (-1 / 4 : ℝ)) = Real.cos (- (Real.pi / 4)) := by
          ring_nf
        rw [h2]
        rw [Real.cos_neg]
        rw [Real.cos_pi_div_four]
      rw [h1, h2]
      field_simp
      <;> ring_nf <;> norm_num