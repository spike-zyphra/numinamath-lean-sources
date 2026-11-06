import Mathlib

theorem calculus_84205 (f : ℝ → ℝ) (a b c : ℝ)
    (h₀ : f = fun x => (x - a) * (x - b) * (x - c))
    (h₁ : 0 < a) (h₂ : 0 < b) (h₃ : 0 < c)
    (h₄ : a ≠ b) (h₅ : a ≠ c) (h₆ : b ≠ c) :
    deriv f a + deriv f b + deriv f c > 0 := by

  have h7 : deriv f a + deriv f b + deriv f c = (1 / 2) * ((a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2) := by

    have h8 : deriv f a = 3 * a ^ 2 - 2 * (a + b + c) * a + (a * b + a * c + b * c) := by
      rw [h₀]
      simp [deriv_mul, deriv_sub, deriv_add, deriv_pow, deriv_id'', mul_comm]
      all_goals
        field_simp
        <;> ring_nf
        <;> norm_num
        <;> ring

    have h9 : deriv f b = 3 * b ^ 2 - 2 * (a + b + c) * b + (a * b + a * c + b * c) := by
      rw [h₀]
      simp [deriv_mul, deriv_sub, deriv_add, deriv_pow, deriv_id'', mul_comm]
      all_goals
        field_simp
        <;> ring_nf
        <;> norm_num
        <;> ring

    have h10 : deriv f c = 3 * c ^ 2 - 2 * (a + b + c) * c + (a * b + a * c + b * c) := by
      rw [h₀]
      simp [deriv_mul, deriv_sub, deriv_add, deriv_pow, deriv_id'', mul_comm]
      all_goals
        field_simp
        <;> ring_nf
        <;> norm_num
        <;> ring

    rw [h8, h9, h10]
    <;> ring_nf <;> norm_num
    all_goals ring_nf <;> norm_num

  rw [h7]

  have h8 : (a - b) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    intro h
    apply h₄
    linarith

  have h9 : (a - c) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    intro h
    apply h₅
    linarith

  have h10 : (b - c) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    intro h
    apply h₆
    linarith

  have h11 : (a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2 > 0 := by
    linarith [h8, h9, h10]

  have h12 : (1 / 2 : ℝ) > 0 := by norm_num

  have h13 : (1 / 2 : ℝ) * ((a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2) > 0 := by
    apply mul_pos
    linarith
    linarith

  linarith