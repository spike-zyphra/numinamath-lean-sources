import Mathlib

theorem algebra_600407 (k : ℝ) (h : ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ a^4-18*a^3+k*a^2+200*a-1984=0 ∧ b^4-18*b^3+k*b^2+200*b-1984=0 ∧ c^4-18*c^3+k*c^2+200*c-1984=0 ∧ d^4-18*d^3+k*d^2+200*d-1984=0 ∧ a*b=-32) :
    k = 86 := by 
  rcases h with ⟨a, b, c, d, ha1, ha2, ha3, hb1, hb2, hne1, ha, hb, hc, hd, h1⟩
  have eq1 : (a - b) * (a^3 + a^2 * b + a * b^2 + b^3 - 18 * (a^2 + a * b + b^2) + k * (a + b) + 200) = 0 := by 
    nlinarith 
  have h2 : a^3 + a^2 * b + a * b^2 + b^3 - 18 * (a^2 + a * b + b^2) + k * (a + b) + 200 = 0 := by
    apply (mul_right_inj' (show a - b ≠ 0 by
      intro h'
      apply ha1
      linarith
    )).mp
    linarith 
  have eq2 : (a + b) * (a^2 + b^2) - 18 * (a^2 + a * b + b^2) + k * (a + b) + 200 = 0 := by
    nlinarith [h1]
  have eq5 : a^2 + b^2 = (a + b) ^ 2 + 64 := by
    have eq5' : a * b = -32 := h1
    nlinarith [sq_nonneg (a - b)]
  have eq6 : a + b = 4 := by 
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by 
      intro h'
      apply ha1
      linarith 
    ), sq_nonneg (a - 4), sq_nonneg (b + 4), sq_nonneg (a * b + 32), sq_nonneg (a + b - 4)]
  have eq7 : k = 86 := by
    rw [show a^2 + b^2 = (a + b) ^ 2 + 64 by linarith [eq5] ] at eq2
    rw [show a^2 + a * b + b^2 = (a + b) ^ 2 - (a * b) by 
      nlinarith
    ] at eq2
    rw [show a * b = -32 by linarith [h1] ] at eq2
    rw [eq6] at eq2
    nlinarith 
  linarith [eq7]