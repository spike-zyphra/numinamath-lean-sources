import Mathlib

theorem number_theory_192107 (a b c : ℕ) (ha : 0 < a) (hb : a ≤ b) (hc : b < c)
    (h : a^2 + b^2 = c^2) : a ≠ 2 := by
  by_contra h1
  rw [show a = 2 by linarith] at h hb
  have h2 : b ≥ 2 := by linarith
  -- 4 + b^2 = c^2
  have eq2 : c ^ 2 = 4 + b ^ 2 := by
    nlinarith
  have h3 : c > b := by linarith
  have h4 : c ≥ 3 := by
    by_contra h4
    push_neg at h4
    have h5 : c < 3 := by linarith
    have h6 : c ≤ 2 := by linarith
    have h7 : b < 3 := by
      nlinarith
    have h8 : b ≤ 2 := by linarith
    interval_cases b <;> interval_cases c
      <;> omega
  -- Now, c ≥ 3 and b ≥ 2. From the equation, (c - b)(c + b) = 4.
  have h5 : c ≤ 3 := by
    nlinarith [sq_nonneg (c - b : ℤ), sq_nonneg ((c + 2) : ℤ),
      sq_nonneg (b : ℕ), sq_nonneg ((c) : ℕ),
      sq_nonneg ((c - 2) : ℤ), sq_nonneg ((b - 2) : ℤ)]
  -- So only possible c = 3.
  have h6 : c = 3 := by
    linarith
  rw [h6] at eq2
  -- So, 9 = 4 + b ^ 2 => b^2 = 5, which is not integer.
  have h7 : b ≤ 3 := by
    nlinarith
  interval_cases b <;> omega