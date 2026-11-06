import Mathlib

open Real

theorem inequalities_221858 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    (logb (a * b * c) a) ^ 3 * logb a b * logb a c ≤ 1 / 27 := by
  have h1 : 0 < a := by linarith
  have h2 : 0 < b := by linarith
  have h3 : 0 < c := by linarith

  have h8 : log a > 0 := by apply log_pos; linarith
  have h9 : log b > 0 := by apply log_pos; linarith
  have h10 : log c > 0 := by apply log_pos; linarith

  have h4 : logb (a * b * c) a = (log a) / (log (a * b * c)) := by
    field_simp [logb]

  have h7 : log (a * b * c) = log a + log b + log c := by
    have h91 : log (a * b * c) = log (a * (b * c)) := by ring_nf
    rw [h91]
    have h92 : log (a * (b * c)) = log a + log (b * c) := by
      rw [log_mul (by linarith) (by
        have h21 : 0 < b := by linarith
        have h22 : 0 < c := by linarith
        positivity
      )]
    have h93 : log (b * c) = log b + log c := by 
      rw [log_mul (by linarith) (by linarith)]
    linarith [h92, h93]

  have h5 : logb a b = (log b) / (log a) := by 
    field_simp [logb]

  have h6 : logb a c = (log c) / (log a) := by 
    field_simp [logb]

  rw [h4, h7, h5, h6]

  have h11 : (log a) * (log b) * (log c) ≤ ((log a + log b + log c) / 3) ^ 3 := by
    nlinarith [sq_nonneg (log a - log b), sq_nonneg (log a - log c), sq_nonneg (log b - log c),
      sq_nonneg ((log a + log b + log c) / 3 - log a), 
      sq_nonneg ((log a + log b + log c) / 3 - log b), 
      sq_nonneg ((log a + log b + log c) / 3 - log c), 
      mul_pos h8 h9, mul_pos h9 h10, mul_pos h8 h10 
    ]

  have h13 : (log a * (log b) * (log c) ) ≤ ((log a + log b + log c) ^ 3 ) / 27 := by 
    nlinarith [h11]

  have h15 : 0 < (log a + log b + log c) := by 
    have ha1 : log a > 0 := h8
    have hb1 : log b > 0 := h9
    have hc1 : log c > 0 := h10
    linarith

  have h16 : 0 < log a := h8

  have h18 : ( (log a) / (log a + log b + log c) ) ^ 3 * ( (log b) / (log a) ) * ( (log c) / (log a) ) = (log a * log b * log c) / ( (log a + log b + log c) ^ 3 ) := by 
    field_simp [h15, h16]
    ring

  have h19 : (27 * (log a * log b * log c) ) ≤ (log a + log b + log c) ^ 3 := by 
    linarith [h13]

  have h20 : (log a * log b * log c) / ( (log a + log b + log c) ^ 3 ) ≤ 1 / 27 := by 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (log a + log b + log c) ]

  linarith [h18, h20]