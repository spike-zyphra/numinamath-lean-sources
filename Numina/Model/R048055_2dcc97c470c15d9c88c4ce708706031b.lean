import Mathlib

theorem algebra_199570 (a b c : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    ∀ x : ℝ, a^2 * (x - b) / (a - b) * (x - c) / (a - c) +
      b^2 * (x - a) / (b - a) * (x - c) / (b - c) +
      c^2 * (x - a) / (c - a) * (x - b) / (c - b) = x^2 := by
  intro x
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : a - c ≠ 0 := by
    intro h
    apply hc
    linarith
  have h3 : b - a ≠ 0 := by
    intro h
    apply ha
    linarith
  have h4 : b - c ≠ 0 := by
    intro h
    apply hb
    linarith
  have h5 : c - a ≠ 0 := by
    intro h
    apply hc
    linarith
  have h6 : c - b ≠ 0 := by
    intro h
    apply hb
    linarith
  field_simp [(show a - b ≠ 0 by assumption), (show a - c ≠ 0 by assumption), 
          (show b - a ≠ 0 by assumption), (show b - c ≠ 0 by assumption), 
          (show c - a ≠ 0 by assumption), (show c - b ≠ 0 by assumption)]
  ring