import Mathlib

theorem algebra_291329 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    (a + b) / ((b - c) * (c - a)) + (b + c) / ((c - a) * (a - b)) +
    (c + a) / ((a - b) * (b - c)) = 0 := by

  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith

  have h2 : b - c ≠ 0 := by
    intro h
    apply hb
    linarith

  have h3 : c - a ≠ 0 := by
    intro h
    apply hc
    linarith

  field_simp [(show b - c ≠ 0 by assumption), (show c - a ≠ 0 by assumption), (show a - b ≠ 0 by assumption), 
          (show (b - c) * (c - a) ≠ 0 by 
            apply mul_ne_zero
            · assumption
            · assumption), (show (c - a) * (a - b) ≠ 0 by 
            apply mul_ne_zero
            · assumption
            · assumption), (show (a - b) * (b - c) ≠ 0 by 
            apply mul_ne_zero
            · assumption
            · assumption)]
  <;> ring