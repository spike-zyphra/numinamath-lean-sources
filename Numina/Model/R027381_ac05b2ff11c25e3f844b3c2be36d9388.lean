import Mathlib

theorem inequalities_286677 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) +
    c^3 / (c^2 + c * a + a^2) ≥ (a + b + c) / 3 := by

  have h11 : 0 < a := by linarith
  have h12 : 0 < b := by linarith
  have h13 : 0 < c := by linarith
  have h21 : 0 < a * b := mul_pos h11 h12
  have h22 : 0 < b * c := mul_pos h12 h13
  have h23 : 0 < c * a := mul_pos h13 h11
  
  have h31 : 0 < a^2 + a * b + b^2 := by
    nlinarith [sq_pos_of_pos h11, sq_pos_of_pos h12, mul_pos h11 h12, 
      sq_nonneg (a - b), sq_nonneg (a + b)
    ]
  
  have h34 : 0 < b^2 + b * c + c^2 := by
    nlinarith [sq_pos_of_pos h12, sq_pos_of_pos h13, mul_pos h12 h13, 
      sq_nonneg (b - c), sq_nonneg (b + c)
    ]

  have h35 : 0 < c^2 + c * a + a^2 := by
    nlinarith [sq_pos_of_pos h13, sq_pos_of_pos h11, mul_pos h13 h11, 
      sq_nonneg (c - a), sq_nonneg (c + a)
    ]
  
  have h41 : a^3 / (a^2 + a * b + b^2) ≥ (2 * a - b) / 3 := by 
    apply (le_div_iff₀ (by nlinarith)).mpr 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
      sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * (a * 2)), sq_nonneg ((b )^2), 
      mul_pos h11 h12, pow_pos h11 2, pow_pos h12 2
    ]
  
  have h42 : b^3 / (b^2 + b * c + c^2) ≥ (2 * b - c) / 3 := by 
    apply (le_div_iff₀ (by nlinarith)).mpr 
    nlinarith [sq_nonneg (b - c), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), 
      sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (b * (b * 2)), sq_nonneg ((c )^2), 
      mul_pos h12 h13, pow_pos h12 2, pow_pos h13 2
    ]
  
  have h43 : c^3 / (c^2 + c * a + a^2) ≥ (2 * c - a) / 3 := by
    apply (le_div_iff₀ (by nlinarith)).mpr 
    nlinarith [sq_nonneg (c - a), sq_nonneg (c * (c - a)), sq_nonneg (a * (c - a)), 
      sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (c * (c * 2)), sq_nonneg ((a )^2), 
      mul_pos h13 h11, pow_pos h13 2, pow_pos h11 2
    ]

  linarith [h41, h42, h43]