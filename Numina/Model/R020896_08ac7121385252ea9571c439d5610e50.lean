import Mathlib

theorem algebra_215925 {a : ℂ} (ha : a ≠ 0) (x : ℝ) (h : a + 1 / a = 2 * Real.cos x) :
    a^4 + 1 / a^4 = 2 * Real.cos (4 * x) := by
  have h1 : a^2 + 1 / a^2 = (a + 1 / a) ^ 2 - 2 := by
    field_simp [ha]
    ring_nf
  have h2 : a^2 + 1 / a^2 = 2 * Real.cos (2 * x) := by
    rw [h1, h]
    have hcos : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := Real.cos_two_mul x
    rw [hcos]
    ring_nf
    <;> simp [pow_two, mul_assoc]
    <;> ring
  have h3 : a^4 + 1 / a^4 = (a^2 + 1 / a^2) ^ 2 - 2 := by
    field_simp [ha]
    ring_nf
  have h4 : a^4 + 1 / a^4 = 2 * Real.cos (4 * x) := by
    rw [h3, h2]
    have hcos : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
      have h1 : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
        rw [show 4 * x = 2 * (2 * x) by ring]
        rw [Real.cos_two_mul]
      exact h1
    rw [hcos]
    ring_nf
    <;> simp [pow_two, mul_assoc]
    <;> ring
  exact h4