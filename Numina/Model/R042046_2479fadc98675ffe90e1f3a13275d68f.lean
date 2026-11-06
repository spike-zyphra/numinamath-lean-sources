import Mathlib

open scoped BigOperators

theorem algebra_276684 (a : ℕ → ℝ)
  (h₀ : a 0 = 1)
  (h₁ : ∀ n, a (n + 1) = a n + 1 / a n) :
  a 99 > 14 := by 
  have h_pos : ∀ n, a n > 0 := by
    intro n 
    induction n with 
    | zero => 
      rw [h₀]
      norm_num 
    | succ n ih =>
      have h1 := h₁ n 
      rw [h1]
      have h2 : a n > 0 := ih 
      have h3 : 0 < a n := by linarith 
      have h4 : 1 / a n > 0 := by 
        apply div_pos 
        all_goals linarith 
      linarith 
  have h2 : ∀ (n : ℕ), a n ^ 2 ≥ 2 * (n : ℝ) + 1 := by
    intro n 
    induction n with 
    | zero => 
      rw [h₀]
      norm_num 
    | succ n ih =>
      have h3 : a (n + 1) = a n + 1 / a n := by 
        specialize h₁ n 
        simpa using h₁ 
      have h4 : a (n + 1) ^ 2 = a n ^ 2 + 2 + 1 / (a n ^ 2) := by 
        rw [h3]
        have h5 : a n > 0 := h_pos n 
        field_simp [h5]
        <;> nlinarith [sq_pos_of_pos h5]
      have h5 : a n > 0 := h_pos n 
      have h6 : 1 / (a n ^ 2) > 0 := by 
        apply div_pos 
        norm_num 
        all_goals nlinarith [sq_pos_of_pos h5]
      have h9 : a (n + 1) ^ 2 ≥ 2 * ((n + 1 : ℕ) : ℝ) + 1 := by
        have h14 : (2 * ((n + 1 : ℕ) : ℝ) + 1 : ℝ) = 2 * (n : ℝ) + 3 := by
          simp at *
          <;> ring_nf 
          <;> norm_num 
        rw [h14]
        have h15 : a (n + 1) ^ 2 = a n ^ 2 + 2 + 1 / (a n ^ 2) := by 
          linarith [h4]
        rw [h15]
        have h16 : a n ^ 2 ≥ 2 * (n : ℝ) + 1 := by 
          simpa using ih 
        have h17 : 1 / (a n ^ 2) > 0 := h6 
        nlinarith [h16, h17, sq_pos_of_pos (show 0 < a n from by linarith [h_pos n]), sq_nonneg (a n)]
      exact h9
  have h3 : a 99 ^ 2 > (196 : ℝ) := by 
    have h4 : a 99 ^ 2 ≥ 2 * (99 : ℝ) + 1 := by 
      apply h2 
    nlinarith [h4]
  have h4 : a 99 > (14 : ℝ) := by
    -- We know that a 99 ^ 2 > 196. From h3
    have h5 : a 99 ^ 2 > (196 : ℝ) := h3
    have h6 : a 99 > 0 := by 
      apply h_pos 
    nlinarith [sq_nonneg (a 99 - 14)]
  exact h4