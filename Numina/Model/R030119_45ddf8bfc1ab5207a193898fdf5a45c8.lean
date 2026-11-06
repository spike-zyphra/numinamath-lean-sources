import Mathlib

theorem algebra_284667 (a : ℝ) (ha : a ≠ 5) (h : ∃ x : ℝ, x < 0 ∧ 5^x = (a + 3) / (5 - a)) :
    a < 1 ∧ a > -3 := by
  rcases h with ⟨x, hx1, heq⟩
  have h1 : (5 : ℝ) ^ x > 0 := by positivity
  have h2 : (5 : ℝ) ^ x < (1 : ℝ) := by
    have h3 : (5 : ℝ) ^ (x) < (5 : ℝ) ^ (0 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      all_goals linarith
    have h4 : (5 : ℝ) ^ (0 : ℝ) = 1 := by
      simp [pow_zero]
    linarith [h3, h4]
  have h3 : (a + 3) / (5 - a) < (1 : ℝ) := by linarith [heq, h2]
  have h4 : (a + 3) / (5 - a) > (0 : ℝ) := by linarith [heq, h1]
  have h5 : a < (1 : ℝ) := by
    by_cases h6 : (5 - a : ℝ) > 0
    · -- case 1, 5 - a > 0, so a < 5
      have h8 : a + 3 < (5 - a : ℝ) := by
        apply (div_lt_iff' h6).mp at h3
        linarith
      nlinarith
    · -- 5 - a ≤ 0
      have h6' : (5 - a : ℝ) ≤ 0 := by 
        by_contra h7
        push_neg at h7
        have h8 : (5 - a : ℝ) > 0 := by linarith
        linarith
      by_cases h7 : (5 - a : ℝ) < (0 : ℝ)
      · -- 5 - a < 0, so a > 5
        have h8 : a + 3 < (0 : ℝ) := by
          apply (lt_div_iff_of_neg' h7).mp at h4
          nlinarith
        nlinarith [sq_nonneg (a + 3), sq_pos_of_ne_zero (show (5 - a : ℝ) ≠ 0 by
          intro h'
          apply ha
          nlinarith
        ), h1, h4, sq_nonneg (x)]
      · -- 5 - a = 0, impossible
        have h8 : (5 - a : ℝ) = 0 := by 
          linarith
        have h9 : a = (5 : ℝ) := by 
          linarith
        contradiction
  have h6 : a > (-3 : ℝ) := by
    by_cases h7 : (5 - a : ℝ) > 0
    · -- case 1, 5 - a > 0, so a < 5
      have h8 : a + 3 > (0 : ℝ) := by
        apply (lt_div_iff' h7).mp at h4
        nlinarith
      linarith
    · -- 5 - a ≤ 0
      have h6' : (5 - a : ℝ) ≤ 0 := by 
        by_contra h7
        push_neg at h7
        have h8 : (5 - a : ℝ) > 0 := by linarith
        linarith
      by_cases h7 : (5 - a : ℝ) < (0 : ℝ)
      · -- 5 - a < 0, so a > 5
        have h8 : a + 3 < (0 : ℝ) := by
          apply (lt_div_iff_of_neg' h7).mp at h4
          nlinarith
        nlinarith [sq_nonneg (a + 3), sq_pos_of_ne_zero (show (5 - a : ℝ) ≠ 0 by
          intro h'
          apply ha
          nlinarith
        ), h1, h4, sq_nonneg (x)]
      · -- 5 - a = 0, impossible
        have h8 : (5 - a : ℝ) = 0 := by 
          linarith
        have h9 : a = (5 : ℝ) := by 
          linarith
        contradiction
  constructor
  · exact_mod_cast h5
  · exact_mod_cast h6