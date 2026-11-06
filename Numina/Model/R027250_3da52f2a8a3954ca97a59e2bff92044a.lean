import Mathlib

open scoped BigOperators

theorem inequalities_37341 (a : ℕ → ℝ)
  (h₀ : a 0 = 1)
  (h₁ : ∀ n, a (n + 1) = a n + 1 / a n) :
  a 99 > 14 := by

  have h2 : ∀ (n : ℕ), a n > 0 := by
    intro n
    induction n with
    | zero => 
      rw [h₀]
      all_goals norm_num
    | succ n ih =>
      have h3 : a (n + 1) = a n + 1 / a n := h₁ n
      rw [h3]
      have h4 : a n > 0 := ih
      have h5 : 1 / a n > 0 := by
        apply div_pos
        norm_num
        linarith
      positivity

  have h3 : ∀ (n : ℕ), a n ^ 2 ≥ 2 * (↑n : ℝ) := by 
    intro n
    induction n with
    | zero => 
      rw [h₀]
      norm_num
    | succ n ih =>
      have h4 : a (n + 1) = a n + 1 / a n := h₁ n
      have h5 : a n > 0 := h2 n
      rw [h4]
      have h7 : (a n + 1 / a n) ^ 2 ≥ 2 * ((↑n + 1 : ℝ)) := by
        have h8 : (a n : ℝ) ^ 2 ≥ 2 * (↑n : ℝ) := ih
        have h5 : a n > 0 := h2 n
        have h6 : (a n + 1 / a n) ^ 2 = (a n : ℝ) ^ 2 + 2 + 1 / (a n ^ 2) := by
          have h7 : a n > 0 := h5
          field_simp
          nlinarith 
        have h9 : (1 / (a n ^ 2) : ℝ) > 0 := by 
          have h10 : a n ^ 2 > 0 := by nlinarith [h5]
          positivity
        have h12 : (a n + 1 / a n) ^ 2 ≥ 2 * ((↑n + 1 : ℝ)) := by
          have h13 : (a n : ℝ) ^ 2 ≥ 2 * (↑n : ℝ) := ih
          have h14 : (a n : ℝ) ^ 2 + 2 ≥ 2 * ((↑n + 1 : ℝ)) := by
            have h15 : (↑n : ℝ) ≥ (0 : ℝ) := by positivity
            nlinarith
          have h16 : (a n + 1 / a n) ^ 2 ≥ (a n : ℝ) ^ 2 + 2 := by
            have h17 : (a n + 1 / a n) ^ 2 = (a n : ℝ) ^ 2 + 2 + 1 / (a n ^ 2) := h6
            rw [h17]
            have h18 : (1 / (a n ^ 2) : ℝ) > 0 := h9
            nlinarith [h18]
          nlinarith
        linarith
      norm_num at h7 ⊢
      linarith

  have h4 : a 99 ^ 2 ≥ 198 := by 
    have h5 : a 99 ^ 2 ≥ 2 * ((99 : ℝ) ) := h3 99
    norm_num at h5 ⊢
    linarith

  have h5 : a 99 > 14 := by 
    have h4' : a 99 ^ 2 > (14 : ℝ) ^ 2 := by 
      nlinarith
    have h10 : a 99 > 0 := h2 99
    have h11 : a 99 > 14 := by
      nlinarith [show a 99 ≥ 0 by linarith [h10]]
    linarith 
  linarith