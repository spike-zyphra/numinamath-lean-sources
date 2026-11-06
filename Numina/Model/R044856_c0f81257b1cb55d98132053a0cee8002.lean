import Mathlib

theorem algebra_223907 {a b c : ℚ} (hdist : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    ∃ q : ℚ, (1 / (a - b)^2 + 1 / (b - c)^2 + 1 / (c - a)^2) = q^2 := by
  rcases hdist with ⟨ha1, hb2, hc3⟩
  use (1 / (a - b) + 1 / (b - c) + 1 / (c - a))
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha1
    linarith
  have h2 : b - c ≠ 0 := by
    intro h
    apply hb2
    linarith
  have h3 : c - a ≠ 0 := by
    intro h
    apply hc3
    linarith
  field_simp [(show a - b ≠ 0 by assumption), (show b - c ≠ 0 by assumption), (show c - a ≠ 0 by assumption), 
          show (a - b) * (b - c) * (c - a) ≠ 0 by
            apply mul_ne_zero
            apply mul_ne_zero
            assumption
            assumption
            assumption]
  <;> ring