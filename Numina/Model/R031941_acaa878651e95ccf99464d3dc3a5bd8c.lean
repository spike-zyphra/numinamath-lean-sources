import Mathlib

  theorem inequalities_43462 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) (habc : a * b * c = 1) :
  3 ≤ a ^ 3 / ((a - b) * (a - c)) + b ^ 3 / ((b - c) * (b - a)) +  c ^ 3 / ((c - a) * (c - b)) := by

  rcases hdist with ⟨ha1, ha2, ha3⟩
  have h1 : a ^ 3 / ((a - b) * (a - c)) + b ^ 3 / ((b - c) * (b - a)) +  c ^ 3 / ((c - a) * (c - b)) = a + b + c := by 
    have h2 : a - b ≠ 0 := by
      intro h
      apply ha1
      linarith
    have h3 : a - c ≠ 0 := by
      intro h
      apply ha2
      linarith
    have h4 : b - c ≠ 0 := by
      intro h
      apply ha3
      linarith
    have h5 : b - a ≠ 0 := by
      intro h
      apply ha1
      linarith
    have h6 : c - a ≠ 0 := by 
      intro h
      apply ha2
      linarith
    have h7 : c - b ≠ 0 := by
      intro h
      apply ha3
      linarith
    field_simp [(show a - b ≠ 0 by exact h2), (show a - c ≠ 0 by exact h3),
              (show b - c ≠ 0 by exact h4), (show b - a ≠ 0 by exact h5), 
              (show c - a ≠ 0 by exact h6), (show c - b ≠ 0 by exact h7)]
    ring_nf
  rw [h1]
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            sq_nonneg (a * b * c - 1), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]