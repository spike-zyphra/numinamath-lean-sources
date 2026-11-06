import Mathlib

theorem inequalities_30944 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    1 / 3 ≤ (a ^ 7 + b ^ 7) / (a ^ 5 + b ^ 5) + (b ^ 7 + c ^ 7) / (b ^ 5 + c ^ 5) +
    (c ^ 7 + a ^ 7) / (c ^ 5 + a ^ 5) := by
  have h1 : 0 < a ^ 5 + b ^ 5 := by positivity
  have h2 : 0 < b ^ 5 + c ^ 5 := by positivity
  have h3 : 0 < c ^ 5 + a ^ 5 := by positivity
  have h4 : (a ^ 7 + b ^ 7) / (a ^ 5 + b ^ 5) ≥ (a ^ 2 + b ^ 2) / 2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a ^ 3 - b ^ 3),
      sq_nonneg (a ^ 4 - b ^ 4), sq_nonneg (a * (a - b)), sq_nonneg (b * (b - a)), 
      mul_pos ha hb
        ]
  have h5 : (b ^ 7 + c ^ 7) / (b ^ 5 + c ^ 5) ≥ (b ^ 2 + c ^ 2) / 2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b ^ 3 - c ^ 3),
      sq_nonneg (b ^ 4 - c ^ 4), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - b)), 
      mul_pos hb hc
        ]
  have h6 : (c ^ 7 + a ^ 7) / (c ^ 5 + a ^ 5) ≥ (c ^ 2 + a ^ 2) / 2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c ^ 3 - a ^ 3),
      sq_nonneg (c ^ 4 - a ^ 4), sq_nonneg (c * (c - a)), sq_nonneg (a * (a - c)), 
      mul_pos hc ha
        ]
  have h7 : (a ^ 7 + b ^ 7) / (a ^ 5 + b ^ 5) + (b ^ 7 + c ^ 7) / (b ^ 5 + c ^ 5) + (c ^ 7 + a ^ 7) / (c ^ 5 + a ^ 5) ≥ (a ^ 2 + b ^ 2) / 2 + (b ^ 2 + c ^ 2) / 2 + (c ^ 2 + a ^ 2) / 2 := by 
    linarith [h4, h5, h6]
  have h8 : (a ^ 2 + b ^ 2) / 2 + (b ^ 2 + c ^ 2) / 2 + (c ^ 2 + a ^ 2) / 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
    ring
  have h9 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 1 / 3 := by
    have h10 : a + b + c = 1 := h
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
      h10, mul_pos ha hb, mul_pos hb hc, mul_pos hc ha
        ]
  linarith [h7, h8, h9]