import Mathlib

theorem number_theory_4795 : IsLeast {y | ∃ x, x > 0 ∧ y > 0 ∧ x = 975 * y ∧ ∃ m, m^2 = x} 39 := by
  constructor
  · -- Let's prove that 39 is in our set.
    use 195 ^ 2
    constructor
    · -- Check x > 0
      norm_num
    constructor
    · -- Check y > 0
      norm_num
    constructor
    · -- Check x = 975 * 39
      norm_num
    use 195
    all_goals
      norm_num
  · -- Let's prove that 39 is minimal
    intro y hy
    rcases hy with ⟨x, hx, hy, hx_eq, m, hm⟩
    by_contra h
    push_neg at h
    have h1 : y ≤ 38 := by linarith
    have h2 : m ≤ 192 := by
      nlinarith [show 975 * (y : ℕ) ≥ 1 by nlinarith]
    interval_cases m <;> try { 
      omega
    }
    all_goals 
      omega