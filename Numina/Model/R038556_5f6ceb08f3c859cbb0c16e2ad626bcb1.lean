import Mathlib

theorem inequalities_149469 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 1) :
    1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (a + c + 1) ≤ 1 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : a * b * c = 1 := h
  have h3 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (a + c + 1) - 1 ≤ 0 := by 
    have h4 : 0 < (a + b + 1) * (b + c + 1) * (a + c + 1) := by positivity
    have h5 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (a + c + 1) - 1 =
        ((b + c + 1) * (a + c + 1) + (a + b + 1) * (a + c + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (a + c + 1)) / ((a + b + 1) * (b + c + 1) * (a + c + 1)) := by 
      field_simp 
      <;> ring
    rw [h5]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Prove numerator is nonpositive
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
    · -- Prove denominator is nonnegative
      positivity
  linarith
  all_goals try { tauto }
  <;> try { nlinarith }
  all_goals try { tauto }
  <;> try { nlinarith }
  all_goals try { tauto }
  <;> try { nlinarith }
  all_goals try { tauto }