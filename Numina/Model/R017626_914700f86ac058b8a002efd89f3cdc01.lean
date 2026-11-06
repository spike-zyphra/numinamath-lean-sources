import Mathlib

theorem algebra_185457 {x y z a : ℝ} (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : z ≠ 0)
    (h₃ : x + y + z = a) (h₄ : 1 / x + 1 / y + 1 / z = 1 / a) :
    x = a ∨ y = a ∨ z = a := by
  have h5 : a ≠ 0 := by
    by_contra h
    have h6 : x + y + z = 0 := by
      rw [h] at h₃
      linarith
    have h₇ : 1 / x + 1 / y + 1 / z = 1 / (0 : ℝ) := by
      rw [h] at h₄
      linarith
    have h₈ : 1 / x + 1 / y + 1 / z = 0 := by
      rw [h₇]
      norm_num
    have h₉ : y * z + x * z + x * y = 0 := by
      have h10 : 1 / x + 1 / y + 1 / z = 0 := by linarith
      have h11 : x * y * z ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        exact h₀
        exact h₁
        exact h₂
      have h12 : (1 / x + 1 / y + 1 / z) * (x * y * z) = 0 := by
        rw [h10]
        norm_num
      have h13 : (1 / x + 1 / y + 1 / z) * (x * y * z) = y * z + x * z + x * y := by
        field_simp [h₀, h₁, h₂]
        <;> ring
      rw [h13] at h12
      linarith
    have h14 : x ^ 2 + y ^ 2 + z ^ 2 = 0 := by
      have h17 : x + y + z = 0 := by linarith
      have h18 : (x + y + z) ^ 2 = 0 := by
        rw [h17]
        norm_num
      have h19 : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (y * z + x * z + x * y) := by
        ring
      rw [h19] at h18
      rw [h₉] at h18
      nlinarith
    have h15 : x = 0 := by
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    contradiction
  have h6 : a * (x * y + y * z + z * x) = x * y * z := by
    have h7 : a ≠ 0 := h5
    field_simp [h₀, h₁, h₂, h5] at h₄
    nlinarith [h₃]
  have h7 : (x + y + z) * (x * y + y * z + z * x) = x * y * z := by
    have h8 : a = x + y + z := by linarith [h₃]
    rw [h8] at h6
    linarith
  have h8 : (x + y) * (x + z) * (y + z) = 0 := by
    nlinarith [h7]
  cases' (mul_eq_zero.mp h8) with h9 h10
  cases' (mul_eq_zero.mp h9) with h11 h12
  · -- x + y = 0
    have h13 : y = -x := by linarith
    have h14 : z = a := by
      have h15 : x + y + z = a := by linarith [h₃]
      rw [show y = -x by linarith [h13]] at h15
      linarith
    right
    right
    linarith
  · -- x + z = 0
    have h14 : z = -x := by linarith
    have h15 : y = a := by
      have h16 : x + y + z = a := by linarith [h₃]
      rw [show z = -x by linarith [h14]] at h16
      linarith
    right
    left
    linarith
  · -- y + z = 0
    have h17 : z = -y := by linarith
    have h18 : x = a := by
      have h19 : x + y + z = a := by linarith [h₃]
      rw [show z = -y by linarith [h17]] at h19
      linarith
    left
    linarith