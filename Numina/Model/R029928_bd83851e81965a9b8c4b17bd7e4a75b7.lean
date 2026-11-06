import Mathlib

theorem inequalities_282578 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a^2 + b^2 + c^2 + d^2 ≤ (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) +
      (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) := by

  have h9 : (a^3 + b^3 + c^3) / (a + b + c) ≥ (a^2 + b^2 + c^2) / 3 := by 
    have h9 : 0 < (a + b + c) := by linarith
    apply (le_div_iff₀ h9).mpr 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)),
      sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)), 
      sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h10 : (b^3 + c^3 + d^3) / (b + c + d) ≥ (b^2 + c^2 + d^2) / 3 := by
    have h10 : 0 < (b + c + d) := by linarith
    apply (le_div_iff₀ h10).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - b), 
      sq_nonneg (b * (b - c)), sq_nonneg (b * (c - d)), sq_nonneg (b * (d - b)), 
      sq_nonneg (c * (b - c)), sq_nonneg (c * (c - d)), sq_nonneg (c * (d - b)), 
      sq_nonneg (d * (b - c)), sq_nonneg (d * (c - d)), sq_nonneg (d * (d - b)), 
      mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
    ]

  have h11 : (c^3 + d^3 + a^3) / (c + d + a) ≥ (c^2 + d^2 + a^2) / 3 := by 
    have h11 : 0 < (c + d + a) := by linarith
    apply (le_div_iff₀ h11).mpr 
    nlinarith [sq_nonneg (c - d), sq_nonneg (d - a), sq_nonneg (a - c), 
      sq_nonneg (c * (c - d)), sq_nonneg (c * (d - a)), sq_nonneg (c * (a - c)), 
      sq_nonneg (d * (c - d)), sq_nonneg (d * (d - a)), sq_nonneg (d * (a - c)), 
      sq_nonneg (a * (c - d)), sq_nonneg (a * (d - a)), sq_nonneg (a * (a - c)), 
      mul_pos hc hd, mul_pos hc ha, mul_pos hd ha
    ]
  have h12 : (d^3 + a^3 + b^3) / (d + a + b) ≥ (d^2 + a^2 + b^2) / 3 := by
    have h12 : 0 < (d + a + b) := by linarith
    apply (le_div_iff₀ h12).mpr
    nlinarith [sq_nonneg (d - a), sq_nonneg (a - b), sq_nonneg (b - d), 
      sq_nonneg (d * (d - a)), sq_nonneg (d * (a - b)), sq_nonneg (d * (b - d)), 
      sq_nonneg (a * (d - a)), sq_nonneg (a * (a - b)), sq_nonneg (a * (b - d)), 
      sq_nonneg (b * (d - a)), sq_nonneg (b * (a - b)), sq_nonneg (b * (b - d)), 
      mul_pos hd ha, mul_pos hd hb, mul_pos ha hb
    ]
  have h13 : (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) + 
      (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥ (a^2 + b^2 + c^2) / 3 + (b^2 + c^2 + d^2) / 3 + (c^2 + d^2 + a^2) / 3 + (d^2 + a^2 + b^2) / 3 := by
    linarith [h9, h10, h11, h12]

  linarith