import Mathlib

theorem algebra_9651 (a b c d : ℕ) (hpos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (hord : a < b ∧ b < c ∧ c < d)
    (h1 : a^2 + b + c + d = 90) (h2 : a + b^2 + c + d = 158) (h3 : a + b + c^2 + d = 204)
    (h4 : a + b + c + d^2 = 320) :
    a + b + c + d = 48 := by
  rcases hpos with ⟨ha, hb, hc, hd⟩
  rcases hord with ⟨h12, h23, h34⟩
  have h5 : a ≤ 9 := by
    nlinarith [h1, h2, h3, h4, sq_nonneg (a - 9 : ℤ), sq_nonneg (b - 10 : ℤ), sq_nonneg (c - 11 : ℤ), sq_nonneg (d - 12 : ℤ)]
  have h6 : a ≤ 9 := h5
  interval_cases a <;> try { 
    omega 
  } <;> try { 
    have h7 : b ≤ 20 := by 
      nlinarith [h1, h2, h3, h4]
    interval_cases b <;> omega 
  }