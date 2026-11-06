import Mathlib

open Real

lemma lemma_1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a < 1) (h2 : b < 1) :
    0 < logb a b := by
  have h3 : log a < 0 := by
    have h4 : log a < log (1 : ℝ) := by
      apply Real.log_lt_log
      all_goals
        try linarith
    have h4' : log (1 : ℝ) = (0 : ℝ) := by
      simp [Real.log_one]
    nlinarith
  have h6 : log b < 0 := by
    have h7 : log b < log (1 : ℝ) := by
      apply Real.log_lt_log
      all_goals
        try linarith
    have h4' : log (1 : ℝ) = (0 : ℝ) := by
      simp [Real.log_one]
    nlinarith
  have h7 : logb a b = log b / log a := by
    field_simp [Real.logb]
  rw [h7]
  apply div_pos_of_neg_of_neg
  all_goals
    try linarith


theorem inequalities_253098 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < 1) (h2 : b < 1) (h3 : c < 1) :
    (logb a b)^4 + (logb b c)^4 + (logb c a)^4 ≥
    logb a b + logb b c + logb c a := by

  have h4 : 0 < logb a b := by
    apply lemma_1 a b ha hb h1 h2

  have h5 : 0 < logb b c := by 
    apply lemma_1 b c hb hc h2 h3

  have h6 : 0 < logb c a := by 
    apply lemma_1 c a hc ha h3 h1

  have h7 : logb a b * logb b c * logb c a = 1 := by
    have h8 : logb a b = log b / log a := by 
      field_simp [logb]
    have h9 : logb b c = log c / log b := by 
      field_simp [logb]
    have h10 : logb c a = log a / log c := by 
      field_simp [logb]
    rw [h8, h9, h10]

    have h11 : log a ≠ 0 := by
      have h12 : log a < 0 := by
        have h4 : log a < log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals
            try linarith
        have h4' : log (1 : ℝ) = (0 : ℝ) := by
          simp [Real.log_one]
        nlinarith
      linarith

    have h12 : log b ≠ 0 := by
      have h13 : log b < 0 := by
        have h4 : log b < log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals
            try linarith
        have h4' : log (1 : ℝ) = (0 : ℝ) := by
          simp [Real.log_one]
        nlinarith
      linarith

    have h13 : log c ≠ 0 := by
      have h14 : log c < 0 := by
        have h4 : log c < log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals
            try linarith
        have h4' : log (1 : ℝ) = (0 : ℝ) := by
          simp [Real.log_one]
        nlinarith
      linarith

    field_simp [h11, h12, h13]
    all_goals
      ring_nf

  have h8 : (logb a b)^4 + (logb b c)^4 + (logb c a)^4 - (logb a b + logb b c + logb c a) ≥ 0 := by
    nlinarith [sq_nonneg ((logb a b)^2 - 1), sq_nonneg ((logb b c)^2 - 1), sq_nonneg ((logb c a)^2 - 1),
        sq_nonneg (logb a b - 1), sq_nonneg (logb b c - 1), sq_nonneg (logb c a - 1),
        sq_nonneg (logb a b * logb b c * logb c a - 1), 
        mul_pos h4 h5, mul_pos h5 h6, mul_pos h4 h6, h7]

  linarith