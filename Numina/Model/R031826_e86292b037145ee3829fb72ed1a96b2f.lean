import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_262962 (f : ℝ → ℝ) (hf : f = λ x => min (x + 2) (x^2 - 6 * x + 8)) :
    {x | f x ≥ 0} = {x | x ∈ Icc (-2) 2 ∨ x ≥ 4} := by 
  ext x
  simp only [Set.mem_setOf_eq, hf]
  constructor
  · -- First, {x | f x ≥ 0} ⊢ {x | x ∈ Icc (-2) 2 ∨ x ≥ 4}
    intro h
    by_cases h2 : (x + 2 : ℝ) ≤ (x ^ 2 - 6 * x + 8)
    · -- Case where x + 2 ≤ x^2 - 6 x + 8, so min(x+2, x^2-6x+8) = x + 2
      have h3 : min (x + 2) (x ^ 2 - 6 * x + 8) = (x + 2) := by 
        apply min_eq_left 
        all_goals 
          nlinarith 
      rw [h3] at h 
      have hx1 : x ≥ (-2 : ℝ) := by linarith
      have h78 : (x - 1) * (x - 6) ≥ 0 := by 
        nlinarith
      have h39 : x ≤ 1 ∨ x ≥ 6 := by
        by_contra h39
        push_neg at h39
        nlinarith
      cases h39 with
      | inl h06 =>
        have hx5 : x ≤ 1 := by linarith
        have hx4 : x ≤ 2 := by nlinarith
        left
        exact ⟨by linarith, by linarith⟩
      | inr h06 =>
        have hx5 : x ≥ 6 := by linarith
        right 
        nlinarith
    · -- Case where x + 2 > x^2 - 6 x + 8, so min(x+2, x^2-6x+8) = x^2 - 6 x + 8
      have h3 : min (x + 2) (x ^ 2 - 6 * x + 8) = (x ^ 2 - 6 * x + 8) := by 
        apply min_eq_right 
        linarith 
      rw [h3] at h 
      by_cases h78 : (x ^ 2 - 6 * x + 8 : ℝ) ≥ 0
      · -- Assume x^2 - 6 x + 8 ≥ 0
        have h7 : x ≤ 2 ∨ x ≥ 4 := by 
          by_contra h 
          push_neg at h 
          nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 4)]
        cases h7 with 
        | inl h8 => 
          left 
          constructor <;> linarith 
        | inr h8 => 
          right 
          linarith 
      · -- Case where x^2 - 6 x + 8 < 0 
        nlinarith 
  · -- Second implication
    intro h 
    rcases h with (h | h)
    · -- Case x ∈ Icc (-2) 2 
      rcases h with ⟨h1, h2⟩ 
      by_cases h2 : (x + 2 : ℝ) ≤ (x ^ 2 - 6 * x + 8)
      · -- Case where x + 2 ≤ x^2 - 6 x + 8, so min(x+2, x^2-6x+8) = x + 2
        have h3 : min (x + 2) (x ^ 2 - 6 * x + 8) = (x + 2) := by 
          apply min_eq_left 
          all_goals 
            nlinarith 
        rw [h3]
        nlinarith 
      · -- Case where x + 2 > x^2 - 6 x + 8, so min(x+2, x^2-6x+8) = x^2 - 6 x + 8
        have h3 : min (x + 2) (x ^ 2 - 6 * x + 8) = (x ^ 2 - 6 * x + 8) := by 
          apply min_eq_right 
          all_goals 
            nlinarith 
        rw [h3]
        nlinarith 
    · -- Case x ≥ 4 
      by_cases h2 : (x + 2 : ℝ) ≤ (x ^ 2 - 6 * x + 8)
      · -- Case where x + 2 ≤ x^2 - 6 x + 8, so min(x+2, x^2-6x+8) = x + 2
        have h3 : min (x + 2) (x ^ 2 - 6 * x + 8) = (x + 2) := by 
          apply min_eq_left 
          all_goals 
            nlinarith 
        rw [h3]
        nlinarith 
      · -- Case where x + 2 > x^2 - 6 x + 8, so min(x+2, x^2-6x+8) = x^2 - 6 x + 8
        have h3 : min (x + 2) (x ^ 2 - 6 * x + 8) = (x ^ 2 - 6 * x + 8) := by
          apply min_eq_right 
          all_goals 
            nlinarith 
        rw [h3]
        nlinarith