import Mathlib

theorem algebra_327521 {a b c : ℝ} (h₀ : a * b * c ≠ 0) (h₁ : a + b + c = 0) :
    a^2 / (b * c) + b^2 / (c * a) + c^2 / (a * b) = 3 := by
  have h2 : a ≠ 0 := by
    by_contra ha
    have h0' : a * b * c = 0 := by
      rw [ha]
      ring
    contradiction
  have h3 : b ≠ 0 := by
    by_contra hb
    have h0' : a * b * c = 0 := by
      rw [hb]
      ring
    contradiction
  have h4 : c ≠ 0 := by
    by_contra hc
    have h0' : a * b * c = 0 := by
      rw [hc]
      ring
    contradiction
  -- Now we can show that each pair multiplication is ≠ 0.
  have eq1 : a^3 + b^3 + c^3 = 3 * (a * b * c) := by
    have h2 : a + b + c = 0 := h₁
    have eq : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by
      ring
    rw [h2] at eq -- because a + b + c = 0
    linarith
  have eq2 : a^2 / (b * c) + b^2 / (c * a) + c^2 / (a * b) = (a^3 + b^3 + c^3) / (a * b * c) := by
    have hb1 : b * c ≠ 0 := by
      apply mul_ne_zero 
      exact h3
      exact h4
    have ha1 : c * a ≠ 0 := by
      apply mul_ne_zero 
      exact h4
      exact h2
    have ha2 : a * b ≠ 0 := by
      apply mul_ne_zero 
      exact h2
      exact h3
    field_simp [hb1, ha1, ha2]
    <;> ring_nf <;> linarith
  rw [eq2]
  have hne : a * b * c ≠ 0 := h₀
  rw [eq1]
  field_simp [hne]
  <;> ring
  all_goals linarith