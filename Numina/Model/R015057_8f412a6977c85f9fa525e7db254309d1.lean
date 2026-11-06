import Mathlib

theorem algebra_66694 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a * Real.sqrt b - c = a) (h2 : b * Real.sqrt c - a = b) (h3 : c * Real.sqrt a - b = c) :
    (a, b, c) = (4, 4, 4) := by
  have h4 : Real.sqrt b ≥ 0 := by positivity
  have h5 : Real.sqrt c ≥ 0 := by positivity
  have h6 : Real.sqrt a ≥ 0 := by positivity
  have eq1 : c = a * (Real.sqrt b - 1) := by
    linarith
  have eq2 : a = b * (Real.sqrt c - 1) := by
    linarith
  have eq3 : b = c * (Real.sqrt a - 1) := by
    linarith
  have eq4 : (Real.sqrt a - 1) * (Real.sqrt b - 1) * (Real.sqrt c - 1) = 1 := by
    have eq5 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
    have eq6 : a * b * c = a * b * c * (Real.sqrt a - 1) * (Real.sqrt b - 1) * (Real.sqrt c - 1) := by
      calc
        a * b * c = (b * (Real.sqrt c - 1)) * (c * (Real.sqrt a - 1)) * (a * (Real.sqrt b - 1)) := by 
          rw [show b * (Real.sqrt c - 1) = a by linarith [eq2]]
          rw [show c * (Real.sqrt a - 1) = b by linarith [eq3]]
          rw [show a * (Real.sqrt b - 1) = c by linarith [eq1]]
          all_goals nlinarith
        _ = a * b * c * (Real.sqrt a - 1) * (Real.sqrt b - 1) * (Real.sqrt c - 1) := by
          ring
    have eq7 : (Real.sqrt a - 1) * (Real.sqrt b - 1) * (Real.sqrt c - 1) = 1 := by
      apply (mul_left_inj' (ne_of_gt eq5)).mp
      linarith
    linarith
  have h9 : Real.sqrt a = 2 := by
    nlinarith [sq_nonneg (Real.sqrt a - 2), sq_nonneg (Real.sqrt b - 2), sq_nonneg (Real.sqrt c - 2),
      Real.sq_sqrt (show 0 ≤ a by positivity), Real.sq_sqrt (show 0 ≤ b by positivity), Real.sq_sqrt (show 0 ≤ c by positivity),
      sq_nonneg (Real.sqrt a * Real.sqrt b * Real.sqrt c - 8)]
  have h10 : Real.sqrt b = 2 := by
    nlinarith [sq_nonneg (Real.sqrt a - 2), sq_nonneg (Real.sqrt b - 2), sq_nonneg (Real.sqrt c - 2),
      Real.sq_sqrt (show 0 ≤ a by positivity), Real.sq_sqrt (show 0 ≤ b by positivity), Real.sq_sqrt (show 0 ≤ c by positivity),
      sq_nonneg (Real.sqrt a * Real.sqrt b * Real.sqrt c - 8)]
  have h11 : Real.sqrt c = 2 := by
    nlinarith [sq_nonneg (Real.sqrt a - 2), sq_nonneg (Real.sqrt b - 2), sq_nonneg (Real.sqrt c - 2),
      Real.sq_sqrt (show 0 ≤ a by positivity), Real.sq_sqrt (show 0 ≤ b by positivity), Real.sq_sqrt (show 0 ≤ c by positivity),
      sq_nonneg (Real.sqrt a * Real.sqrt b * Real.sqrt c - 8)]
  have ha4 : a = 4 := by
    calc
      a = Real.sqrt a ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      _ = 2 ^ 2 := by
        rw [h9]
      _ = 4 := by norm_num
  have hb4 : b = 4 := by
    calc
      b = Real.sqrt b ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      _ = 2 ^ 2 := by
        rw [h10]
      _ = 4 := by norm_num
  have hc4 : c = 4 := by
    calc
      c = Real.sqrt c ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      _ = 2 ^ 2 := by
        rw [h11]
      _ = 4 := by norm_num
  simp [ha4, hb4, hc4]