import Mathlib

theorem algebra_2296 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a ≠ 0) (h₂ : b ≠ 0) (h₃ : c ≠ 0) : (b * c + a * c) / (a * b) + (a * b + a * c) / (b * c) + (a * b + b * c) / (a * c) = -3 := by
  have h4 : a + b = -c := by
    linarith
  have h5 : b + c = -a := by
    linarith
  have h6 : a + c = -b := by
    linarith
  have eq1 : (b * c + a * c) / (a * b) = -c^2 / (a * b) := by
    have h7 : b * c + a * c = c * (b + a) := by
      ring
    rw [h7]
    rw [show b + a = -c by linarith]
    field_simp [(show a ≠ 0 by exact h₁), (show b ≠ 0 by exact h₂), (show c ≠ 0 by exact h₃)]
    <;> ring
  have eq2 : (a * b + a * c) / (b * c) = -a^2 / (b * c) := by
    have h7 : a * b + a * c = a * (b + c) := by
      ring
    rw [h7]
    rw [show b + c = -a by linarith]
    field_simp [(show a ≠ 0 by exact h₁), (show b ≠ 0 by exact h₂), (show c ≠ 0 by exact h₃)]
    <;> ring
  have eq3 : (a * b + b * c) / (a * c) = -b^2 / (a * c) := by
    have h7 : a * b + b * c = b * (a + c) := by
      ring
    rw [h7]
    rw [show a + c = -b by linarith]
    field_simp [(show a ≠ 0 by exact h₁), (show b ≠ 0 by exact h₂), (show c ≠ 0 by exact h₃)]
    <;> ring
  rw [eq1, eq2, eq3]
  have h8 : a^3 + b^3 + c^3 = 3 * a * b * c := by
    have h9 : a + b + c = 0 := h₀
    have h10 : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - a * b - a * c - b * c) := by
      ring
    rw [h9] at h10
    linarith
  have h9 : -c^2 / (a * b) + -a^2 / (b * c) + -b^2 / (a * c) = - ( (c^3 + a^3 + b^3) / (a * b * c) ) := by
    field_simp [(show a ≠ 0 by exact h₁), (show b ≠ 0 by exact h₂), (show c ≠ 0 by exact h₃)]
    ring
  rw [h9]
  rw [show c^3 + a^3 + b^3 = 3 * a * b * c by linarith [h8]]
  have h10 : (3 * a * b * c : ℝ) / (a * b * c) = 3 := by
    field_simp [(show a ≠ 0 by exact h₁), (show b ≠ 0 by exact h₂), (show c ≠ 0 by exact h₃)]
    <;> nlinarith
  rw [h10]
  <;> linarith