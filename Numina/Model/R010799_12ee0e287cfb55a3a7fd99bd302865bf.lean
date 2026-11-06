import Mathlib
theorem algebra_607686 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c + a * b * c = 4) : (1 + a / b + c * a) * (1 + b / c + a * b) * (1 + c / a + b * c) ≥ 27:= by
  have hab : 0 < a * b:= mul_pos ha hb
  have hbc : 0 < b * c:= mul_pos hb hc
  have hac : 0 < a * c:= mul_pos ha hc
  have habc : 0 < a * b * c:= mul_pos (mul_pos ha hb) hc

  -- \left(1 + \frac{\mathrm{a}}{\mathrm{~b}} + \mathrm{ca}\right)\left(1 + \frac{\mathrm{b}}{\mathrm{c}} + \mathrm{ab}\right)\left(1 + \frac{\mathrm{c}}{\mathrm{a}} + \mathrm{bc}\right) = \frac{(a + b + a b c)(b + c + a b c)(c + a + a b c)}{a b c}
  have h1 : (1 + a / b + c * a) * (1 + b / c + a * b) * (1 + c / a + b * c) =
      (a + b + a * b * c) * (b + c + a * b * c) * (c + a + a * b * c) / (a * b * c):= by
    field_simp
    ring
  
  have h2 : (a + b + a * b * c) = 4 - c:= by 
    nlinarith [h]
  
  have h3 : (b + c + a * b * c) = 4 - a:= by 
    nlinarith [h]
  
  have h4 : (c + a + a * b * c) = 4 - b:= by 
    nlinarith [h]

  rw [h1]
  have h5 : (a + b + a * b * c) * (b + c + a * b * c) * (c + a + a * b * c) = (4 - c) * (4 - a) * (4 - b):= by 
    rw [h2, h3, h4]
  
  rw [h5]

  apply (le_div_iff₀ (by positivity)).mpr 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]