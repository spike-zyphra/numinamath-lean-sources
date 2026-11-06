import Mathlib

open Real

theorem inequalities_267680 (a b c d m n : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hm : 0 < m) (hn : 0 < n) :
    sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) ≥ sqrt (a * b) + sqrt (c * d) := by

  have h1 : 0 < m * a + n * c := by positivity
  have h2 : 0 < (b / m) + (d / n) := by
    have hb' : 0 < b := hb
    have hd' : 0 < d := hd
    have hm' : 0 < m := hm
    have hn' : 0 < n := hn
    positivity

  have h3 : (sqrt (a * b) + sqrt (c * d)) ^ 2 ≤ (sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) ) ^ 2 := by

    have h4 : (sqrt (a * b) + sqrt (c * d)) ^ 2 = (sqrt (a * b)) ^ 2 + (sqrt (c * d)) ^ 2 + 2 * (sqrt (a * b) * sqrt (c * d)) := by ring

    have h5 : (sqrt (a * b)) ^ 2 = a * b := by 
      rw [Real.sq_sqrt]
      positivity

    have h6 : (sqrt (c * d)) ^ 2 = c * d := by 
      rw [Real.sq_sqrt]
      positivity

    have h7 : sqrt (a * b) * sqrt (c * d) = sqrt ((a * b) * (c * d)) := by
      rw [← Real.sqrt_mul (by positivity)]

    have h8 : (sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) ) ^ 2 = (sqrt (m * a + n * c)) ^ 2 * (sqrt ((b / m) + (d / n))) ^ 2 := by ring

    have h9 : (sqrt (m * a + n * c)) ^ 2 = m * a + n * c := by
      rw [Real.sq_sqrt]
      positivity

    have h10 : (sqrt ((b / m) + (d / n)) ) ^ 2 = (b / m) + (d / n) := by
      rw [Real.sq_sqrt]
      positivity

    have h11 : (sqrt (a * b) + sqrt (c * d)) ^ 2 = a * b + c * d + 2 * sqrt ((a * b) * (c * d)) := by
      rw [h4, h5, h6, h7]
      all_goals
        nlinarith

    have h12 : (sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) ) ^ 2 = (m * a + n * c) * ((b / m) + (d / n)) := by
      rw [h8, h9, h10]

    rw [h11, h12]

    have h13 : (m * a + n * c) * ((b / m) + (d / n)) = a * b + c * d + (m * a * d / n) + (n * c * b / m) := by 
      field_simp [hm.ne', hn.ne']
      ring

    rw [h13]

    have h14 : 0 ≤ (m * a * d / n) + (n * c * b / m) - 2 * sqrt ((a * b) * (c * d)) := by 
      have h15 : (m * a * d / n) + (n * c * b / m) ≥ 2 * sqrt ((a * b) * (c * d)) := by
        have h16 : sqrt ((a * b) * (c * d)) = Real.sqrt (a * b * (c * d)) := by ring
        rw [h16] 
        have h17a : (m * a * d / n) ≥ 0 := by positivity
        have h17b : (n * c * b / m) ≥ 0 := by positivity
        have h17 : (m * a * d / n) + (n * c * b / m) ≥ 2 * Real.sqrt (a * b * (c * d)) := by
          have h19 : Real.sqrt (a * b * (c * d)) = Real.sqrt ((m * a * d / n) * (n * c * b / m)) := by
            field_simp [hm.ne', hn.ne']
            all_goals 
              ring
          rw [h19] 
          nlinarith [Real.sqrt_nonneg ((m * a * d / n) * (n * c * b / m)), Real.sq_sqrt (show 0 ≤ (m * a * d / n) * (n * c * b / m) by positivity), 
                     sq_nonneg ((m * a * d / n) - (n * c * b / m)), sq_nonneg (Real.sqrt ((m * a * d / n) * (n * c * b / m)) )
                     ]
        linarith 
      linarith 

    nlinarith [Real.sqrt_nonneg ((a * b) * (c * d)), Real.sqrt_nonneg (a * b * (c * d)), Real.sqrt_nonneg (m * a * d / n * (n * c * b / m)), Real.sqrt_nonneg (a * b * (c * d)), Real.sq_sqrt (show 0 ≤ (a * b) * (c * d) by positivity)]

  have h31 : sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) ≥ 0 := by positivity
  have h32 : sqrt (a * b) + sqrt (c * d) ≥ 0 := by positivity

  nlinarith [Real.sqrt_nonneg (m * a + n * c), Real.sqrt_nonneg ((b / m) + (d / n)), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), 
             Real.sq_sqrt (show 0 ≤ (m * a + n * c) by positivity), Real.sq_sqrt (show 0 ≤ (b / m) + (d / n) by positivity), 
             Real.sq_sqrt (show 0 ≤ (a * b) by positivity), Real.sq_sqrt (show 0 ≤ (c * d) by positivity)
             ]