import Mathlib

theorem number_theory_43844 (n : ℕ) :
    ∃ x y k, x > 0 ∧ y > 0 ∧ x.Coprime y ∧ k > 1 ∧ 3^n = x^k + y^k ↔ n = 2 := by 
  use 2, 1, 3
  constructor
  · -- Forward direction: if the equation holds, then n = 2
    intro h
    rcases h with ⟨h1, h2, h3, h4, heq⟩
    have eq1 : 3 ^ n = 9 := by
      norm_num at heq ⊢
      linarith 
    have eq2 : n = 2 := by
      have h1 : 3 ^ n = 9 := eq1
      have h2 : n = 2 := by
        have h3 : 3 ^ n = 3 ^ 2 := by
          rw [h1]
          all_goals norm_num
        have h4 : n = 2 := by 
          exact Nat.pow_right_injective (by norm_num) h3
        assumption
      assumption
    assumption
  · -- Backward direction: if n = 2, then the equation holds
    intro h
    rw [h]
    constructor
    · norm_num 
    constructor 
    · norm_num 
    constructor 
    · norm_num [Nat.Coprime] 
    constructor 
    · norm_num 
    · norm_num