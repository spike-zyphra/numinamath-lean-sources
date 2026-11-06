import Mathlib

theorem number_theory_258412 :
  {n : ℕ | n % 7 = 2 ∧ n % 8 = 4 ∧ n / 7 = (n / 8) + 7} = {380} := by 
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward implication: If n is in the set, then n = 380
    intro h
    rcases h with ⟨h1, h2, h3⟩
    have h7 : n = 380 := by
      omega
    exact h7
  · -- Backward direction: If n = 380, then it's in the set
    intro h
    rw [h]
    constructor
    · -- 380 % 7 = 2
      norm_num
    constructor
    · -- 380 % 8 = 4
      norm_num
    · -- 380 / 7 = (380 / 8) + 7
      norm_num