import Mathlib

theorem inequalities_603638
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b > c)
    (h' : a + c > b)
    (h'' : b + c > a) :
    6 ≤ (a + b) / (b + c - a) + (b + c) / (c + a - b) + (c + a) / (a + b - c) := by
  have ha1 : 0 < b + c - a := by linarith
  have ha2 : 0 < c + a - b := by linarith
  have ha3 : 0 < a + b - c := by linarith
  have h1 : (a + b) / (b + c - a) + (b + c) / (c + a - b) + (c + a) / (a + b - c) - 6 ≥ 0 := by 
    have h3 : ( (a + b) / (b + c - a) + (b + c) / (c + a - b) + (c + a) / (a + b - c) - 6 ) =
        ( (a + b) * (c + a - b) * (a + b - c) + (b + c) * (b + c - a) * (a + b - c) + (c + a) * (b + c - a) * (c + a - b) - 6 * ((b + c - a) * (c + a - b) * (a + b - c)) ) / ((b + c - a) * (c + a - b) * (a + b - c)) := by
      field_simp
      ring
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
      mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
      mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
    ]
    positivity
  linarith