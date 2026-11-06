import Mathlib

theorem inequalities_597120
    (a b c x y z : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    a * x / (a + x) + b * y / (b + y) + c * z / (c + z) ≤
    ((a + b + c) * (x + y + z)) / (a + b + c + x + y + z) := by 
  have h1 : 0 < a + x := by
    linarith 
  have h2 : 0 < b + y := by
    linarith 
  have h3 : 0 < c + z := by
    linarith 
  have h4 : 0 < a + b + c + x + y + z := by
    linarith [ha, hb, hc, hx, hy, hz]

  have h5 : a * x / (a + x) + b * y / (b + y) + c * z / (c + z) - ((a + b + c) * (x + y + z)) / (a + b + c + x + y + z) ≤ 0 := by 
    have pos1 : 0 < (a + x) * (b + y) * (c + z) * (a + b + c + x + y + z) := by positivity 
    have h6 : a * x / (a + x) + b * y / (b + y) + c * z / (c + z) - ((a + b + c) * (x + y + z)) / (a + b + c + x + y + z) = 
      (a * x * (b + y) * (c + z) * (a + b + c + x + y + z) + 
        b * y * (a + x) * (c + z) * (a + b + c + x + y + z) + 
        c * z * (a + x) * (b + y) * (a + b + c + x + y + z) - 
        (a + b + c) * (x + y + z) * (a + x) * (b + y) * (c + z)) / 
      ((a + x) * (b + y) * (c + z) * (a + b + c + x + y + z)) := by 
      field_simp 
      ring 
    rw [h6] at *
    apply div_nonpos_of_nonpos_of_nonneg 
    · -- Prove numerator is nonpositive 
      nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (b * z - c * y), sq_nonneg (c * x - a * z), 
        sq_nonneg (a * (y + z) - b * (x + z)), sq_nonneg (b * (x + z) - c * (x + y)), sq_nonneg (c * (x + y) - a * (x + y)), 
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
        mul_pos (show 0 < a by linarith) (show 0 < x by linarith), 
        mul_pos (show 0 < b by linarith) (show 0 < y by linarith), 
        mul_pos (show 0 < c by linarith) (show 0 < z by linarith)
      ]
    all_goals 
      positivity
  linarith