import Mathlib

theorem algebra_89013 : {(a, b, c) : ℝ × ℝ × ℝ | 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a ^ 2 + a * b = c ∧ b ^ 2 + b * c = a ∧ c ^ 2 + c * a = b} = {(0, 0, 0), (1 / 2, 1 / 2, 1 / 2)} := by

  ext ⟨a, b, c⟩
  simp
  constructor
  · -- Assume (a, b, c) are in the set, so they satisfy the constraints
    rintro ⟨ha, hb, hc, h1, h2, h3⟩

    have h4 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

    have h5 : a - b = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

    have h6 : b - c = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

    have h7 : a = b := by linarith
    have h8 : b = c := by linarith
    have h9 : a = c := by linarith

    -- From $a = b = c$ and from equation 1: $a^2 + a * a = c$ 
    -- But since all are equal: $a^2 + a * a = 2a^2 = a$
    -- So quadratic equation: $2a^2 - a = 0$
    have h10 : a * (2 * a - 1) = 0 := by
      have h11 : a ^ 2 + a * b = c := h1
      rw [show b = a by linarith [h7]] at h11
      rw [show c = a by linarith [h7, h8]] at h11
      nlinarith

    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- case $h11$, so $a = 0$, then all variables are 0.
      have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith [h7, ha0]
      have hc0 : c = 0 := by linarith [h7, hb0, h8]
      left
      simp [ha0, hb0, hc0]
    · -- case $h12$, so $2 * a - 1 = 0$
      have ha1 : a = 1 / 2 := by linarith
      have hb1 : b = 1 / 2 := by linarith [h7, ha1]
      have hc1 : c = 1 / 2 := by linarith [h7, hb1, h8]
      right
      simp [ha1, hb1, hc1]
  · -- Show that the given solutions satisfy the constraints.
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- (0, 0, 0)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (1/2, 1/2, 1/2)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num