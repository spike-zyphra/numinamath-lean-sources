import Mathlib

theorem inequalities_117149 (x a : ℝ) (hx : 0 < x) (ha : x < a) :
    (a - x)^6 - 3 * a * (a - x)^5 + 5 / 2 * a^2 * (a - x)^4 - 1 / 2 * a^4 * (a - x)^2 < 0 := by
  have h1 : 0 < a - x := by nlinarith
  have h2 : 0 < a := by nlinarith
  have h3 : 0 < x := by linarith
  have h4 : (a - x)^6 - 3 * a * (a - x)^5 + 5 / 2 * a^2 * (a - x)^4 - 1 / 2 * a^4 * (a - x)^2 =
      (a - x)^2 * ((a - x)^4 - 3 * a * (a - x)^3 + 5 / 2 * a^2 * (a - x)^2 - 1 / 2 * a^4) := by
    ring
  rw [h4]
  have h5 : 0 < (a - x)^2 := by
    nlinarith
  have h7 : (a - x)^4 - 3 * a * (a - x)^3 + 5 / 2 * a^2 * (a - x)^2 - 1 / 2 * a^4 < 0 := by
    have hk1 : 0 < a - x := by linarith
    have hk2 : 0 < a := by linarith
    have hk0 : a - x > 0 := by linarith
    have hk3 : a > 0 := by linarith
    have hk4 : (a - x) / a > 0 := by
      apply div_pos
      all_goals linarith
    set k := (a - x) / a with hk
    have hk5 : k > 0 := by
      nlinarith
    have hk6 : k < 1 := by
      have h9 : a - x < a := by nlinarith
      have h10 : (a - x) / a < (a) / a := by
        apply (div_lt_div_right (by linarith)).mpr
        nlinarith
      have h11 : (a) / a = 1 := by
        field_simp
        all_goals linarith
      linarith [h10, h11, show 0 < a by linarith]
    have h9 : (a - x)^4 - 3 * a * (a - x)^3 + 5 / 2 * a^2 * (a - x)^2 - 1 / 2 * a^4 =
        (1 / 2) * a^4 * (2 * k^4 - 6 * k^3 + 5 * k^2 - 1) := by
      have hk' : (a - x) = a * k := by
        field_simp at hk ⊢
        nlinarith
        all_goals linarith
      rw [hk']
      ring_nf
      <;> field_simp
      <;> ring_nf <;> nlinarith
      all_goals linarith
      <;> field_simp
      all_goals nlinarith
    rw [h9]
    have ha_pos : a > 0 := by linarith
    have ha4_pos : 0 < a^4 := by positivity
    have hk7 : 2 * k ^ 4 - 6 * k ^ 3 + 5 * k ^ 2 - 1 < 0 := by
      have hk8 : (k - 1) ^ 2 > 0 := by
        nlinarith [show k ≠ 1 by nlinarith]
      have hk9 : 2 * k ^ 2 - 2 * k - 1 < 0 := by
        nlinarith [sq_nonneg (k - (1 + Real.sqrt 3) / 2), sq_nonneg (k - (1 - Real.sqrt 3) / 2), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          mul_pos (show 0 < k by linarith) (show 0 < 1 - k by nlinarith)
        ]
      have hk10 : 2 * k ^ 4 - 6 * k ^ 3 + 5 * k ^ 2 - 1 = (k - 1) ^ 2 * (2 * k ^ 2 - 2 * k - 1) := by ring
      rw [hk10]
      apply mul_neg_of_pos_of_neg
      exact hk8
      exact hk9
      all_goals nlinarith
      all_goals nlinarith
    nlinarith [ha4_pos, hk7, mul_pos ha4_pos (show 0 < (1 / 2 : ℝ) by norm_num)]
    all_goals nlinarith
  nlinarith [h5, h7, mul_pos (show 0 < (a - x) by linarith) (show 0 < (a) by linarith)]
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith