import Mathlib

theorem inequalities_599269 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    1 / 3 ≤ (a ^ 7 + b ^ 7) / (a ^ 5 + b ^ 5) + (b ^ 7 + c ^ 7) / (b ^ 5 + c ^ 5) +
    (c ^ 7 + a ^ 7) / (c ^ 5 + a ^ 5) := by

  have h1 : 0 < a ^ 5 + b ^ 5 := by positivity
  have h2 : 0 < b ^ 5 + c ^ 5 := by positivity
  have h3 : 0 < c ^ 5 + a ^ 5 := by positivity

  have h4 : (a ^ 7 + b ^ 7) / (a ^ 5 + b ^ 5) ≥ (a ^ 2 + b ^ 2) / 2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
      pow_pos ha 1, pow_pos hb 1, pow_pos ha 2, pow_pos hb 2, 
      pow_pos ha 3, pow_pos hb 3, pow_pos ha 4, pow_pos hb 4, 
      sq_nonneg (a^4 - b^4), sq_nonneg (a^3 - b^3)]

  have h5 : (b ^ 7 + c ^ 7) / (b ^ 5 + c ^ 5) ≥ (b ^ 2 + c ^ 2) / 2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), 
      pow_pos hb 1, pow_pos hc 1, pow_pos hb 2, pow_pos hc 2, 
      pow_pos hb 3, pow_pos hc 3, pow_pos hb 4, pow_pos hc 4, 
      sq_nonneg (b^4 - c^4), sq_nonneg (b^3 - c^3)]

  have h6 : (c ^ 7 + a ^ 7) / (c ^ 5 + a ^ 5) ≥ (c ^ 2 + a ^ 2) / 2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), 
      pow_pos hc 1, pow_pos ha 1, pow_pos hc 2, pow_pos ha 2, 
      pow_pos hc 3, pow_pos ha 3, pow_pos hc 4, pow_pos ha 4, 
      sq_nonneg (c^4 - a^4), sq_nonneg (c^3 - a^3)]

  have h7 : (a ^ 7 + b ^ 7) / (a ^ 5 + b ^ 5) + (b ^ 7 + c ^ 7) / (b ^ 5 + c ^ 5) + (c ^ 7 + a ^ 7) / (c ^ 5 + a ^ 5) ≥ 
    (a ^ 2 + b ^ 2) / 2 + (b ^ 2 + c ^ 2) / 2 + (c ^ 2 + a ^ 2) / 2 := by
    linarith [h4, h5, h6]

  have h8 : (a ^ 2 + b ^ 2) / 2 + (b ^ 2 + c ^ 2) / 2 + (c ^ 2 + a ^ 2) / 2 = a^2 + b^2 + c^2 := by
    ring_nf

  have h9 : (a ^ 7 + b ^ 7) / (a ^ 5 + b ^ 5) + (b ^ 7 + c ^ 7) / (b ^ 5 + c ^ 5) + (c ^ 7 + a ^ 7) / (c ^ 5 + a ^ 5) ≥ a^2 + b^2 + c^2 := by
    linarith [h8, h7]

  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
    h, sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
    sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3)]