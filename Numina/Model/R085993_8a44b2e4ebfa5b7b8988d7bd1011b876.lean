import Mathlib

theorem algebra_275471 :
    IsLeast {x | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + (1 / (2 * a : ℚ)) + (1 / (3 * a : ℚ)) = 1 / (b ^ 2 - 2 * b) ∧ x = a + b} 50 := by
  constructor
  · -- Show 50 is in the set
    use 44, 6
    all_goals norm_num
  · -- Show that 50 is the smallest
    intro x hx
    rcases hx with ⟨a, b, ha, hb, heq, hx⟩
    by_contra h
    push_neg at h
    have h1 : a ≤ 49 := by omega
    have h2 : b ≤ 49 := by omega
    interval_cases a <;> interval_cases b <;> norm_num at heq ⊢ <;> omega