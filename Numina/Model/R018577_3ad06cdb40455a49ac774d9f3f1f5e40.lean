import Mathlib

open Real Set

theorem inequalities_311156 (c : ℝ) :
    (∀ a b : ℝ, max (max (|a + b|) (|a - b|)) (|2006 - b|) ≥ c) ↔
    c ≤ 1003 := by
  constructor
  · -- Forward direction: if the inequality holds for all a, b, then c ≤ 1003.
    intro h
    have h1 := h 0 1003
    norm_num [abs_of_pos, abs_of_neg, max_eq_left, max_eq_right] at h1 ⊢
    all_goals linarith
  · -- Backward direction: if c ≤ 1003, then the inequality holds for all a, b.
    intro h a b
    have h1 : max (max (|a + b|) (|a - b|)) (|2006 - b|) ≥ 1003 := by
      by_contra h2
      push_neg at h2
      have h21 : |a + b| < (1003 : ℝ) := by
        have h3 : max (max (|a + b|) (|a - b|)) (|2006 - b|) < (1003 : ℝ) := by linarith [h2]
        have h4 : |a + b| < (1003 : ℝ) := by
          have h5 : max (max (|a + b|) (|a - b|)) (|2006 - b|) ≥ |a + b| := by
            simp [max_le_iff]
          linarith [h5, h3]
        linarith
      have h22 : |a - b| < (1003 : ℝ) := by
        have h3 : max (max (|a + b|) (|a - b|)) (|2006 - b|) < (1003 : ℝ) := by linarith [h2]
        have h4 : |a - b| < (1003 : ℝ) := by
          have h5 : max (max (|a + b|) (|a - b|)) (|2006 - b|) ≥ |a - b| := by
            simp [max_le_iff]
          linarith [h5, h3]
        linarith
      have h23 : |(2006 : ℝ) - b| < (1003 : ℝ) := by
        have h3 : max (max (|a + b|) (|a - b|)) (|2006 - b|) < (1003 : ℝ) := by linarith [h2]
        have h4 : |(2006 : ℝ) - b| < (1003 : ℝ) := by
          have h5 : max (max (|a + b|) (|a - b|)) (|2006 - b|) ≥ |(2006 : ℝ) - b| := by
            simp [max_le_iff]
          linarith [h5, h3]
        linarith
      have h24 : 1003 < b := by
        linarith [abs_lt.mp h23]
      have h25 : b < (3009 : ℝ) := by
        linarith [abs_lt.mp h23]
      have h26 : -1003 < a := by
        cases' abs_lt.mp h21 with h27 h28
        cases' abs_lt.mp h22 with h29 h30
        linarith
      have h27 : a < (1003 : ℝ) := by
        cases' abs_lt.mp h21 with h28 h29
        cases' abs_lt.mp h22 with h30 h31
        linarith
      -- Derive contradiction
      have h28 : a < (0 : ℝ) := by
        cases' abs_lt.mp h21 with h29 h30
        nlinarith
      have h29 : 0 < a := by
        cases' abs_lt.mp h22 with h31 h32
        nlinarith
      linarith
    linarith