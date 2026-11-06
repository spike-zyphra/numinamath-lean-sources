import Mathlib

theorem inequalities_598076 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (y ^ 2 - x ^ 2) / (z + x) + (z ^ 2 - y ^ 2) / (x + y) + (x ^ 2 - z ^ 2) / (y + z) ≥ 0 := by
  have h₁ : 0 < z + x := by linarith only [hx, hz]
  have h₂ : 0 < x + y := by linarith only [hx, hy]
  have h₃ : 0 < y + z := by linarith only [hy, hz]
  have h4 : (y ^ 2 - x ^ 2) / (z + x) + (z ^ 2 - y ^ 2) / (x + y) + (x ^ 2 - z ^ 2) / (y + z) = ((y ^ 2 - x ^ 2) * (x + y) * (y + z) + (z ^ 2 - y ^ 2) * (z + x) * (y + z) + (x ^ 2 - z ^ 2) * (z + x) * (x + y)) / ((z + x) * (x + y) * (y + z)) := by
    field_simp
    ring
  rw [h4]
  have h5 : (y ^ 2 - x ^ 2) * (x + y) * (y + z) + (z ^ 2 - y ^ 2) * (z + x) * (y + z) + (x ^ 2 - z ^ 2) * (z + x) * (x + y) ≥ 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
       sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
       sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (y + z - x),
       mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos (show 0 < x * y from by nlinarith) (show 0 < x * y from by nlinarith), sq_nonneg (x * y * z - x * y * z)
       ]
  have h6 : (z + x) * (x + y) * (y + z) > 0 := by positivity
  apply div_nonneg
  linarith
  positivity
  <;> nlinarith
  all_goals try positivity
  all_goals try linarith
  all_goals try positivity
  all_goals try nlinarith
  all_goals try linarith
  all_goals try positivity
  all_goals try nlinarith
  all_goals try linarith
  all_goals try positivity
  all_goals try nlinarith
  all_goals try linarith
  all_goals try positivity
  all_goals try nlinarith
  all_goals try linarith
  all_goals try positivity
  all_goals try nlinarith
  all_goals try linarith
  all_goals try positivity
  all_goals try nlinarith
  all_goals try linarith
  all_goals try positivity
  all_goals try nlinarith
  all_goals try linarith
  all_goals try positivity
  <;> try { tauto } <;> try { omega }
  <;> try { tauto } <;> try { omega }
  all_goals try { tauto } <;> try { omega }
  <;> try { tauto } <;> try { omega }