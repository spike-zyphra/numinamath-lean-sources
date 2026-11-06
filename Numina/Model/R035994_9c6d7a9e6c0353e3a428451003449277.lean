import Mathlib

theorem algebra_251617 (a b c d e f : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hd : 1 < d) (he : 1 < e) (hf : 1 < f) (h1 : a * b = c) (h2 : b * c = d)
    (h3 : c * d = e) (h4 : d * e = f) (h5 : e * f = 540) :
    a + b + c + d + e + f ≤ 686 := by

  have h6 : e ∣ 540 := by 
    use f
    linarith

  have h7 : e ≤ 540 := by 
    exact Nat.le_of_dvd (by linarith) h6

  have h8 : f = 540 / e := by 
    rw [← h5]
    field_simp [show e > 0 by omega]

  have h9 : e ≥ 2 := by 
    omega

  have h10 : e ≥ 2 := by 
    omega

  interval_cases e <;> norm_num [h8] at h5 h4 h3 h2 h1 h6 h7 hd ha hb hc hd he hf <;> 
    try { 
      tauto
    }
  all_goals 
    try { 
      norm_num at *
      <;> nlinarith 
    }
  all_goals 
    try { 
      nlinarith [mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (b : ℕ) by linarith)]
    }