import Mathlib

theorem number_theory_211946 (a b c d p q : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hp : 0 < p) (hq : 0 < q) (h1 : a * d - b * c = 1) (h2 : (a / b : ℚ) > p / q)
    (h3 : p / q > (c / d : ℚ)) :
    q ≥ b + d ∧ (q = b + d → p = a + c) := by

  have h2' : (a : ℚ) / (b : ℚ) > (p : ℚ) / (q : ℚ) := by
    linarith [h2]

  have h3' : (p : ℚ) / (q : ℚ) > (c : ℚ) / (d : ℚ) := by
    linarith [h3]

  have h4 : a * q > b * p := by
    have h5 : (a : ℚ) * (q : ℚ) > (b : ℚ) * (p : ℚ) := by
      have h6 : (a / b : ℚ) > (p / q : ℚ) := h2'
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h6
      linarith
    exact_mod_cast h5

  have h5' : p * d > q * c := by
    have h4' : (p : ℚ) * (d : ℚ) > (q : ℚ) * (c : ℚ) := by
      have h7 : (p / q : ℚ) > (c / d : ℚ) := h3'
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h7
      linarith
    exact_mod_cast h4'

  constructor
  · -- Show q ≥ b + d
    nlinarith [sq_nonneg (a - c), sq_nonneg (d - b), sq_nonneg (p - a - c), sq_nonneg (q - b - d),
              h1, mul_pos ha hb, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, mul_pos hd hp, mul_pos hb hp, mul_pos ha hp]
  · -- Show that if q = b + d, then p = a + c
    intro hq_eq
    nlinarith [sq_nonneg (p - a - c), sq_nonneg (q - b - d), h1, mul_pos ha hb, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, mul_pos hd hp, mul_pos hb hp, mul_pos ha hp, hq_eq]