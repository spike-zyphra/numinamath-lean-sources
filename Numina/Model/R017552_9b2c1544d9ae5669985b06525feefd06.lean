import Mathlib

theorem algebra_310558 (a x : ℝ) (ha : a ≠ 0) (hx : x ≠ 1) :
    (a * x ^ 2 / (x - 1) - 2 * a = a ^ 2 + 1) ↔
    (x = a + 1 ∨ x = 1 + 1 / a) := by

  constructor
  · -- Assume the equation holds, prove the solutions
    intro h
    have h1 : x - 1 ≠ 0 := by
      intro h2
      apply hx
      linarith
    have h2 : a * x ^ 2 - 2 * a * (x - 1) = (a ^ 2 + 1) * (x - 1) := by
      have h1 : x - 1 ≠ 0 := h1
      field_simp [h1] at h ⊢
      linarith
    have h3 : a * x ^ 2 - (2 * a + a ^ 2 + 1) * x + (2 * a + a ^ 2 + 1) = 0 := by 
      linarith
    have h4 : (x - (a + 1)) * (x - (1 + 1 / a)) = 0 := by
      field_simp [ha] at *
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- case x = a + 1
      left
      linarith
    · -- case x = 1 + 1 / a
      right
      field_simp [ha] at h6 ⊢
      all_goals linarith
  · -- Assume the solutions, prove the equation.
    rintro (h | h)
    · -- x = a + 1
      rw [h]
      have h1 : (a + 1 : ℝ) - 1 ≠ 0 := by 
        by_contra h'
        have : a = 0 := by linarith
        contradiction
      field_simp [h1, ha] at *
      <;> ring_nf
      <;> nlinarith
    · -- x = 1 + 1 / a
      rw [h]
      have h2 : (1 + 1 / a : ℝ) - 1 ≠ 0 := by
        by_contra h'
        have h3 : 1 / a = 0 := by linarith
        field_simp [ha] at h3
      field_simp [h2, ha] at *
      <;> ring_nf
      <;> nlinarith