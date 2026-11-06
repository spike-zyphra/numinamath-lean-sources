import Mathlib

theorem algebra_304057 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b + c = 32) (h2 : (b + c - a) / (b * c) + (c + a - b) / (c * a) +
      (a + b - c) / (a * b) = 1 / 4) :
    (Real.sqrt a)^2 + (Real.sqrt b)^2 = (Real.sqrt c)^2 ∨
    (Real.sqrt a)^2 + (Real.sqrt c)^2 = (Real.sqrt b)^2 ∨
    (Real.sqrt b)^2 + (Real.sqrt c)^2 = (Real.sqrt a)^2 := by 
  have ha1 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (show 0 ≤ a by linarith)
  have hb1 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (show 0 ≤ b by linarith)
  have hc1 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt (show 0 ≤ c by linarith)
  rw [ha1, hb1, hc1]
  have hc' : c = 32 - a - b := by linarith [h1]
  have hp1 : a * b * c > 0 := by positivity
  have eq1 : a * (b + c - a) + b * (c + a - b) + c * (a + b - c) = 1 / 4 * (a * b * c) := by
    have pos1 : a * b * c > 0 := by positivity
    have eq3 : (b + c - a) / (b * c) + (c + a - b) / (c * a) + (a + b - c) / (a * b) = 
        (a * (b + c - a) + b * (c + a - b) + c * (a + b - c)) / (a * b * c) := by
      field_simp [show 0 < b * c from by nlinarith [hb, hc], show 0 < c * a from by nlinarith [hc, ha], show 0 < a * b from by nlinarith [ha, hb]]
      ring
    rw [eq3] at h2
    have eq4 : a * (b + c - a) + b * (c + a - b) + c * (a + b - c) = 1 / 4 * (a * b * c) := by
      field_simp [show a*b*c ≠ 0 from by positivity] at h2 ⊢
      nlinarith
    assumption
  rw [hc'] at eq1
  by_cases h : a + b = c
  · -- Assume a + b = c, prove the first disjunction
    left
    nlinarith [h, hc']
  by_cases h' : a + c = b
  · -- Assume a + c = b, prove the second disjunction
    right
    left
    nlinarith [h', hc']
  by_cases h'' : b + c = a
  · -- Assume b + c = a, prove the third disjunction
    right
    right
    nlinarith [h'', hc']
  push_neg at *
  have eq2 : (a + b - c) * (a - b + c) * (b + c - a) = 0 := by
    have h3 : c = 32 - a - b := by linarith [h1]
    rw [h3] at *
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (32 - a - b)), sq_nonneg (b - (32 - a - b)),
      sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (b + (32 - a - b) - a), 
      mul_pos ha hb, mul_pos hb (show 0 < 32 - a - b by nlinarith [h1, show c > 0 by nlinarith]), 
      mul_pos ha (show 0 < 32 - a - b by nlinarith [h1, show c > 0 by nlinarith])
    ]
  cases' (mul_eq_zero.mp eq2) with eq3 eq4
  cases' (mul_eq_zero.mp eq3) with eq5 eq6
  · -- Case where $a+b-c = 0$
    left
    nlinarith
  · -- Case where $a-b+c = 0$
    right
    left
    nlinarith
  · -- Case where $b+c-a = 0$
    right
    right
    nlinarith