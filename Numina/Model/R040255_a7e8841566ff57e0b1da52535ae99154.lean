import Mathlib


theorem algebra_111050 (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = a^2) (h2 : y^2 + y * z + z^2 = b^2) (h3 : x^2 + x * z + z^2 = c^2) :
    x * y + y * z + x * z = let p := (a + b + c) / 2; 4 * √(p * (p - a) * (p - b) * (p - c) / 3) := by
  have h4 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h5 : x * y + y * z + x * z > 0 := by
    positivity
  have h7 : (x * y + y * z + x * z) ^ 2 = (16 * (( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 ) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
  have h10 : (x * y + y * z + x * z) = (4 * Real.sqrt ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 )) := by
    have h9 : (4 * Real.sqrt ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 )) ^ 2 = (16 * (( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 ) := by
      have h9 : Real.sqrt ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 ) ^ 2 = ( ( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 := by
        have h10 : ( ( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 ≥ 0 := by
          have h12 : ( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ≥ 0 := by
            have ha4 : 0 < a := ha
            have hb4 : 0 < b := hb
            have hc4 : 0 < c := hc
            nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
          nlinarith
        rw [Real.sq_sqrt (by linarith)]
      calc
        (4 * Real.sqrt ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 )) ^ 2
          = 16 * (Real.sqrt ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 ) ^ 2) := by ring
        _ = 16 * ( ( ( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 ) := by
          rw [h9]
        _ = (16 * (( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 ) := by ring
    have h30 : x * y + y * z + x * z ≥ 0 := by
      positivity
    have h110 : (4 * Real.sqrt ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 )) ≥ 0 := by
      positivity
    have h120 : (x * y + y * z + x * z) ^ 2 = (4 * Real.sqrt ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 )) ^ 2 := by
      nlinarith [Real.sqrt_nonneg ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 )]
    have h130 : (x * y + y * z + x * z) = (4 * Real.sqrt ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 )) := by
      nlinarith [Real.sqrt_nonneg ((( (a + b + c) / 2 ) * (( (a + b + c) / 2 ) - a) * (( (a + b + c) / 2 ) - b) * (( (a + b + c) / 2 ) - c) ) / 3 )]
    exact h130
  simp only [h10]
  all_goals linarith