import Mathlib

theorem algebra_95985 {a b : ℝ} (h₀ : a ≠ b) (h₁ : a / b + (a + 10 * b) / (b + 10 * a) = 2) :
    a / b = 0.8 := by
  have h2 : b ≠ 0 := by
    by_contra h
    have h3 : a / b = 0 := by
      rw [h]
      norm_num
    rw [h3] at h₁
    have h5 : (a + 10 * b) / (b + 10 * a) = a / (10 * a) := by
      rw [show b = (0 : ℝ) by linarith]
      <;> ring_nf <;> field_simp [(show a ≠ (0 : ℝ) by
        by_contra h'
        have : a = 0 := by linarith
        have h5 : a = b := by
          rw [this, h]
        contradiction
      )
      ]
    rw [h5] at h₁
    have h6 : a / (10 * a) = 1 / 10 := by
      have h7 : a ≠ 0 := by
        by_contra h'
        have : a = 0 := by linarith
        have h5 : a = b := by
          rw [this, h]
        contradiction
      field_simp [h7]
      <;> nlinarith
    rw [h6] at h₁
    norm_num at h₁
  -- Prove that b + 10a ≠ 0
  have h3 : b + 10 * a ≠ 0 := by
    by_contra h
    have h4 : (a + 10 * b) / (b + 10 * a) = 0 := by
      rw [show b + 10 * a = (0 : ℝ) by linarith]
      norm_num
    rw [h4] at h₁
    have h5 : a / b = 2 := by
      linarith
    have h8 : b = -10 * a := by
      linarith
    have h9 : a / b = -1 / 10 := by
      rw [show b = -10 * a by linarith [h8]]
      have h7 : a ≠ 0 := by
        by_contra h'
        have h8' : a = 0 := by linarith
        have h5 : a = b := by
          rw [h8', show b = -10 * a by linarith [h8]]
          all_goals nlinarith
        contradiction
      field_simp [h7]
      <;> ring
    rw [h9] at h5
    norm_num at h5
  -- Now, we can clear denominators
  have eq1 : a * (b + 10 * a) + (a + 10 * b) * b = 2 * b * (b + 10 * a) := by
    have h4 : b ≠ 0 := h2
    have h3' : b + 10 * a ≠ 0 := h3
    have eq2 : a / b + (a + 10 * b) / (b + 10 * a) = (a * (b + 10 * a) + (a + 10 * b) * b) / (b * (b + 10 * a)) := by
      field_simp [h4, h3']
      <;> ring
    rw [eq2] at h₁
    have eq3 : (a * (b + 10 * a) + (a + 10 * b) * b) / (b * (b + 10 * a)) = 2 := h₁
    have h5 : b * (b + 10 * a) ≠ 0 := by
      apply mul_ne_zero
      exact h4
      exact h3'
    field_simp [h5] at eq3 ⊢
    all_goals nlinarith
  -- We can then solve the polynomial equation.
  have eq2 : 5 * a ^ 2 - 9 * a * b + 4 * b ^ 2 = 0 := by
    nlinarith [eq1]
  have eq3 : (5 * a - 4 * b) * (a - b) = 0 := by
    nlinarith [eq2]
  cases' (mul_eq_zero.mp eq3) with h4 h5
  · -- Case 5a - 4b = 0
    have h6 : 5 * a = 4 * b := by
      linarith
    have h7 : a / b = 4 / 5 := by
      have h8 : b ≠ 0 := h2
      have eq4 : a = 4 / 5 * b := by
        linarith [h6]
      rw [eq4]
      field_simp [h8]
      <;> ring
    rw [h7]
    norm_num
  · -- Case a - b = 0
    exfalso
    apply h₀
    linarith