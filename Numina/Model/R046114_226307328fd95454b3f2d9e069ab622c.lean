import Mathlib

theorem algebra_15434 (P : ℝ) (r : ℝ) (hP : P = 10) (hr : r = 0.15) :
    IsLeast {x : ℕ | x > 0 ∧ (P * (1 + r * x)) ≥ 2 * P} 7 := by
  constructor
  · -- Show that 7 is in the set
    constructor
    · norm_num
    · -- Show that when x = 7, P * (1 + r * 7) ≥ 2 * P
      rw [hP, hr]
      norm_num
  · -- Show that no integer less than 7 is in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have : n < 7 := h
    have h2 : n < 7 := by linarith
    -- Show that for n < 7, the inequality does not hold
    have h3 : P * (1 + r * (n : ℝ)) < 2 * P := by
      rw [hP, hr]
      have hn4 : n ≤ 6 := by omega
      have hx : (n : ℝ) ≤ 6 := by
        have h4 : n ≤ 6 := by omega
        exact_mod_cast h4
      norm_num
      nlinarith
    -- Contradicts the hypothesis that n is in the set
    have h4 : (P * (1 + r * (n : ℝ)) : ℝ) ≥ (2 * P : ℝ) := by
      simpa using hn2
    linarith [h3, h4]