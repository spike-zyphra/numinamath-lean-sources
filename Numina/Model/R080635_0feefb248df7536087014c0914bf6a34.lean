import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22337 :
  IsGreatest {x | ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ x = (a + b) / (a * b + 1)} 1 := by
  constructor
  · -- Show that 1 is in the set
    use 1, 0
    norm_num
  · -- Show that 1 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, ha1, ha2, hb1, hb2, hx⟩
    have h1 : a * b + 1 > 0 := by
      nlinarith
    have h2 : a + b ≤ a * b + 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b)]
    have h4 : (a + b) / (a * b + 1) ≤ 1 := by
      have h2' : a + b ≤ (a * b + 1) := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b)]
      have h3 : a * b + 1 > 0 := by 
        nlinarith [sq_nonneg a, sq_nonneg b]
      have h4 : (a + b) / (a * b + 1) ≤ (a * b + 1) / (a * b + 1) := by
        apply (div_le_div_right h3).mpr
        linarith
      have h4' : (a * b + 1) / (a * b + 1) = 1 := by
        field_simp
      linarith [h4, h4']
    linarith [hx, h4]