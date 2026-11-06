import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_174783 (a b : ℝ) :
  {x : ℝ | a^2 * x + b^2 * (1 - x) ≥ (a * x + b * (1 - x))^2} =
  if b = a then univ else {x | 0 ≤ x ∧ x ≤ 1} := by
  by_cases h : b = a
  · -- If b = a.
    rw [if_pos h]
    ext x
    simp [h]
    all_goals nlinarith
  · -- If b ≠ a.
    have hb : b ≠ a := by
      intro h1
      apply h
      linarith
    rw [if_neg hb]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and]
    constructor
    · -- Assume $a^2 x + b^2 (1 - x) \geq (a x + b (1 - x))^2$, prove $0 \leq x \wedge x \leq 1$.
      intro h
      have h1 : x * (1 - x) ≥ 0 := by
        have h2 : (a - b) ^ 2 > 0 := by 
          apply pow_two_pos_of_ne_zero 
          intro h4 
          apply hb 
          all_goals linarith 
        nlinarith [sq_nonneg (x * (a - b)), sq_nonneg ((1 - x) * (a - b)), sq_nonneg (x - 1 / 2 : ℝ), sq_pos_of_ne_zero (show (a - b) ≠ 0 by intro h4; apply hb; linarith)]
      have hx1 : 0 ≤ x := by
        nlinarith [sq_nonneg (x - 1 / 2 : ℝ), h1]
      have hx2 : x ≤ 1 := by
        nlinarith [sq_nonneg (x - 1 / 2 : ℝ), h1]
      constructor
      · exact hx1
      · exact hx2
    · -- Assume 0 ≤ x ∧ x ≤ 1, prove a ^ 2 x + b ^ 2 (1 - x) ≥ (a x + b (1 - x)) ^ 2.
      rintro ⟨hx0, hx1⟩
      have h1 : a ^ 2 * x + b^2 * (1 - x) ≥ (a * x + b * (1 - x)) ^ 2 := by
        have h2 : x * (1 - x) ≥ 0 := by 
          nlinarith
        have h4 : (a - b) ^ 2 * (x * (1 - x)) ≥ 0 := by
          have h2' : (a - b) ^ 2 > 0 := by 
            apply pow_two_pos_of_ne_zero 
            intro h4 
            apply hb 
            all_goals linarith 
          nlinarith
        nlinarith [sq_nonneg (x * (a - b)), sq_nonneg ((1 - x) * (a - b)), sq_nonneg (x - 1 / 2 : ℝ), sq_pos_of_ne_zero (show (a - b) ≠ 0 by intro h4; apply hb; linarith)]
      linarith