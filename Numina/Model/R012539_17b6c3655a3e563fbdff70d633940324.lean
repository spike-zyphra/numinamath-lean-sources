import Mathlib

theorem inequalities_318349
    (a b c A B C k : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hA : 0 < A)
    (hB : 0 < B)
    (hC : 0 < C)
    (h : a + A = b + B)
    (h' : b + B = c + C)
    (hk : c + C = k)
    : a * B + b * C + c * A < k ^ 2 := by 
  have eq1 : A = k - a := by
    nlinarith 
  have eq2 : B = k - b := by
    nlinarith
  have eq3 : C = k - c := by
    nlinarith 
  have h1 : 0 < k - a := by nlinarith
  have h2 : 0 < k - b := by nlinarith 
  have h3 : 0 < k - c := by nlinarith 
  rw [eq1, eq2, eq3]
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
          sq_pos_of_pos (show 0 < k - a by nlinarith), 
          sq_pos_of_pos (show 0 < k - b by nlinarith), 
          sq_pos_of_pos (show 0 < k - c by nlinarith), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < k - a by nlinarith) (show 0 < k - b by nlinarith), 
          mul_pos (show 0 < k - a by nlinarith) (show 0 < k - c by nlinarith), 
          mul_pos (show 0 < k - b by nlinarith) (show 0 < k - c by nlinarith), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg ((k - a) - (k - b)), sq_nonneg ((k - a) - (k - c)), 
          sq_nonneg ((k - b) - (k - c)), 
          mul_pos ha (show 0 < k - a by nlinarith), 
          mul_pos ha (show 0 < k - b by nlinarith), 
          mul_pos ha (show 0 < k - c by nlinarith), 
          mul_pos hb (show 0 < k - a by nlinarith), 
          mul_pos hb (show 0 < k - b by nlinarith), 
          mul_pos hb (show 0 < k - c by nlinarith), 
          mul_pos hc (show 0 < k - a by nlinarith), 
          mul_pos hc (show 0 < k - b by nlinarith), 
          mul_pos hc (show 0 < k - c by nlinarith)
        ]