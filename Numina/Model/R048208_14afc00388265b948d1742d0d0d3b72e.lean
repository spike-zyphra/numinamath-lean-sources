import Mathlib

theorem algebra_288628 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a * b + 2 * a - b = 58) (h2 : b * c + 4 * b + 2 * c = 300) (h3 : c * d - 6 * c + 4 * d = 101) :
    (a, b, c, d) = (3, 26, 7, 13) ∨ (a, b, c, d) = (15, 2, 73, 7) := by

  have h1' : a * b + 2 * a = b + 58 := by
    omega

  have eq1 : a * (b + 2) = b + 58 := by
    nlinarith

  have h4 : b ≤ 58 := by
    by_contra h
    push_neg at h
    have h5 : a * (b + 2) = b + 58 := by
      nlinarith
    have h6 : a ≤ 58 := by
      nlinarith
    interval_cases a <;> omega

  have h7 : b ≤ 58 := h4

  have h8 : c ≤ 147 := by
    nlinarith [h2]

  interval_cases b <;> norm_num at h1 h2
  <;> try { 
    omega 
  }
  <;> try { 
    interval_cases c <;> norm_num at h1 h2 h3
    <;> norm_num [Prod.ext_iff, Prod.ext_iff] at *
    <;> omega 
  }
  <;> omega