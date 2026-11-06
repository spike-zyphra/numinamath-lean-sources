import Mathlib

theorem algebra_184646 (t : ℝ) (ht : t ≠ -1 ∧ t ≠ -2 ∧ t ≠ -3) :
    ((1 / (t^2 + 3 * t + 2) + 2 * t / (t^2 + 4 * t + 3) +
      1 / (t^2 + 5 * t + 6))^2) * ((t - 3)^2 + 12 * t) / 2 = 2 := by
  rcases ht with ⟨ht1, ht2, ht3⟩
  have h1 : t + 1 ≠ 0 := by
    intro h
    apply ht1
    linarith
  have h2 : t + 2 ≠ 0 := by
    intro h
    apply ht2
    linarith
  have h3 : t + 3 ≠ 0 := by
    intro h
    apply ht3
    linarith
  have eq1 : 1 / (t^2 + 3 * t + 2) + 2 * t / (t^2 + 4 * t + 3) + 1 / (t^2 + 5 * t + 6) = 2 / (t + 3) := by
    have h4 : t^2 + 3 * t + 2 = (t + 1) * (t + 2) := by
      ring
    have h5 : t^2 + 4 * t + 3 = (t + 1) * (t + 3) := by
      ring
    have h6 : t^2 + 5 * t + 6 = (t + 2) * (t + 3) := by
      ring
    rw [h4, h5, h6]
    have h7 : (t + 1) * (t + 2) ≠ 0 := by
      apply mul_ne_zero
      · exact h1
      · exact h2
    have h8 : (t + 1) * (t + 3) ≠ 0 := by
      apply mul_ne_zero
      · exact h1
      · exact h3
    have h9 : (t + 2) * (t + 3) ≠ 0 := by
      apply mul_ne_zero
      · exact h2
      · exact h3
    field_simp [(show t + 1 ≠ 0 by exact h1), (show t + 2 ≠ 0 by exact h2), (show t + 3 ≠ 0 by exact h3), h7, h8, h9]
    ring_nf
  have eq2 : ((1 / (t^2 + 3 * t + 2) + 2 * t / (t^2 + 4 * t + 3) +
      1 / (t^2 + 5 * t + 6))^2) * ((t - 3)^2 + 12 * t) / 2 = 2 := by
    rw [eq1]
    have h7 : (t - 3)^2 + 12 * t = (t + 3) ^ 2 := by
      ring
    rw [h7]
    have h8 : t + 3 ≠ 0 := by
      exact h3
    field_simp [h8]
    <;> nlinarith
  exact eq2