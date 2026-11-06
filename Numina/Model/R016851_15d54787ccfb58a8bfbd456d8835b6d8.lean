import Mathlib

theorem number_theory_254050 :
    IsLeast {x | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ 96 * a ^ 2 = b ^ 3 ∧ x = a} 12 := by 
  constructor
  · -- Show that 12 is indeed in our set.
    use 12, 24
    all_goals norm_num
  · -- We now prove 12 is minimal.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, heq, hx⟩
    by_contra h
    push_neg at h
    have h1 : a < 12 := by 
      linarith [h, hx]
    have h2 : b ≤ 24 := by
      nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), heq, h1, ha]
    interval_cases a <;> try { 
      omega 
    } <;> interval_cases b <;> norm_num at heq ha hb <;> all_goals 
      omega 
      <;> tauto