import Mathlib

theorem number_theory_53698 (a : ℕ → ℕ)
    (h₀ : a 10 = 10)
    (h₁ : ∀ n > 10, a n = 100 * a (n - 1) + n) :
    IsLeast {n | 10 < n ∧ 99 ∣ a n} 45 := by 
  constructor
  · -- Show 45 is in the set
    constructor
    · norm_num -- Show 10 < 45
    · -- Show 99 divides a 45
      norm_num [h₀, h₁]
      <;> native_decide
  · -- Show no integer less than 45 is in the set
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h2 : n ≤ 44 := by linarith
    interval_cases n <;> norm_num [h₀, h₁] at hn2 <;> all_goals omega