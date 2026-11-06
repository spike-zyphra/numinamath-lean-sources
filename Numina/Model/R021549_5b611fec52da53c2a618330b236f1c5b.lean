import Mathlib

theorem algebra_3982 {a x : ℝ} (h : a ≠ x) (hx2 : x ^ 2 ≠ a * x) : x / (x - a) + a ^ 2 / (a * x - x ^ 2) = 1 + a / x := by

  have h1 : a * x - x ^ 2 = x * (a - x) := by 
    ring

  have h2 : x - a = -(a - x) := by 
    ring

  have h3 : x ≠ 0 := by
    by_contra h4
    have h4 : x = 0 := by linarith
    rw [h4] at hx2
    have h0 : (0 : ℝ) ^ 2 ≠ (0 : ℝ) * a := by
      simpa using hx2
    simp at h0

  have h4 : a - x ≠ 0 := by
    intro h5
    apply h
    linarith

  have eq1 : x / (x - a) = -x / (a - x) := by
    rw [show x - a = -(a - x) by linarith]
    rw [div_neg]
    <;> ring

  have eq3 : a ^ 2 / (a * x - x ^ 2) = a ^ 2 / (x * (a - x)) := by 
    rw [show a * x - x ^ 2 = x * (a - x) by ring]

  rw [eq1, eq3]

  have h5 : x * (a - x) ≠ 0 := by
    apply mul_ne_zero
    · -- Show x ≠ 0
      exact h3
    · -- Show a - x ≠ 0
      exact h4

  have h6 : x ≠ 0 := h3

  field_simp [(show a - x ≠ 0 by exact h4), h6, h5, (show x - a ≠ 0 by
    intro h7
    apply h
    linarith
  )]
  <;> ring