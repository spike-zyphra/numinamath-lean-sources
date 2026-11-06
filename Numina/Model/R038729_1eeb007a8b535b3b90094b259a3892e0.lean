import Mathlib

theorem algebra_5929 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x * y * z + x * y + x * z + y * z + x + y + z = 587) (h2 : 2 * (y + 1) = z + 1) :
    x + y + z = 24 := by
  have h1' : (x + 1) * (y + 1) * (z + 1) = 588 := by
    nlinarith 
  have h2' : z + 1 = 2 * (y + 1) := by 
    linarith 
  have h3 : (x + 1) * (y + 1) ^ 2 = 294 := by
    rw [show z + 1 = 2 * (y + 1) by linarith [h2']] at h1'
    nlinarith 
  have h6 : y = 6 := by
    have h7 : (y + 1) ^ 2 ∣ 294 := by
      use (x + 1)
      all_goals nlinarith [h3]
    have h8 : y + 1 ≥ 2 := by 
      nlinarith 
    have h5 : (y + 1) ≤ 17 := by
      by_contra h 
      push_neg at h
      have h10 : (y + 1) ^ 2 ≥ 18 * 18 := by
        nlinarith 
      nlinarith 
    interval_cases k : y + 1 <;> try { 
      omega 
    }
    all_goals 
      norm_num at h3 
      try { 
        omega 
      }
  have h7 : x = 5 := by 
    nlinarith [h3, show y = 6 by linarith [h6]]
  have h8 : z = 13 := by 
    nlinarith [show y = 6 by linarith [h6], h2']
  linarith