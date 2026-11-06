import Mathlib

theorem inequalities_98819 (a b c x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) :
    min (x / (a * b + a * c)) (y / (a * c + b * c)) < (x + y) / (a * b + b * c) := by

  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * c := mul_pos ha hc
  have h3 : 0 < b * c := mul_pos hb hc
  have h4 : 0 < a * b + a * c := by positivity
  have h5 : 0 < a * c + b * c := by positivity
  have h6 : 0 < a * b + b * c := by positivity
  -- Assume the minimum is greater or equal, reach contradiction
  by_contra h
  -- negation is the minimum is greater than (x+y)/(ab+bc)
  push_neg at h

  have h7 : x / (a * b + a * c) ≥ (x + y) / (a * b + b * c) := by
    cases min_cases (x / (a * b + a * c)) (y / (a * c + b * c)) with
    | inl h1 =>
      linarith [h, h1]
    | inr h2 =>
      linarith [h, h2]

  have h8 : y / (a * c + b * c) ≥ (x + y) / (a * b + b * c) := by 
    cases min_cases (x / (a * b + a * c)) (y / (a * c + b * c)) with
    | inl h1 =>
      linarith [h, h1]
    | inr h2 =>
      linarith [h, h2]

  have h9 : x * (a * b + b * c) ≥ (x + y) * (a * b + a * c) := by
    have h9 : x / (a * b + a * c) ≥ (x + y) / (a * b + b * c) := h7
    apply (div_le_div_iff (by positivity) (by positivity)).mp at h9
    linarith

  have h10 : y * (a * b + b * c) ≥ (x + y) * (a * c + b * c) := by 
    have h10 : y / (a * c + b * c) ≥ (x + y) / (a * b + b * c) := h8
    apply (div_le_div_iff (by positivity) (by positivity)).mp at h10
    linarith

  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha (show 0 < x * y by nlinarith), 
    mul_pos hb hc, mul_pos ha (show 0 < y by linarith), 
    mul_pos hb (show 0 < y by linarith), 
    mul_pos hx hy 
    ]