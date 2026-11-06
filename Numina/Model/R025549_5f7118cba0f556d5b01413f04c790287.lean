import Mathlib

theorem number_theory_137486 (n p : ℕ) (hn : n ≠ 0) (hp : Nat.Prime p) :
    ∃ m : ℕ, m^2 = n + p / n ↔ (n = 1 ∧ p = 3) ∨ (n = 3 ∧ p = 3) := by
  by_cases h : (n = 1 ∧ p = 3) ∨ (n = 3 ∧ p = 3)
  · -- If the conditions hold, set m=2
    use 2
    constructor
    · -- Assume m^2 = n + p / n, prove (n = 1 ∧ p = 3) ∨ (n = 3 ∧ p = 3)
      intro h1
      tauto
    · -- Assume (n = 1 ∧ p = 3) ∨ (n = 3 ∧ p = 3), prove m^2 = n + p / n
      intro h2
      rcases h2 with (h2 | h2)
      · 
        rcases h2 with ⟨r1, r2⟩
        have eq1 : n = 1 := r1
        have eq2 : p = 3 := r2
        have h_eq : (2 : ℕ)^2 = n + p / n := by
          rw [eq1, eq2]
          all_goals norm_num 
        exact h_eq
      · 
        rcases h2 with ⟨r1, r2⟩
        have eq1 : n = 3 := r1
        have eq2 : p = 3 := r2
        have h_eq : (2 : ℕ)^2 = n + p / n := by 
          rw [eq1, eq2]
          all_goals norm_num 
        exact h_eq
  · -- If not, set m=0
    use 0
    constructor
    · -- Assume m^2 = n + p / n, prove (n = 1 ∧ p = 3) ∨ (n = 3 ∧ p = 3)
      intro h1
      exfalso
      have h2 : n + p / n > 0 := by
        have hn1 : n ≥ 1 := by 
          omega
        have h3 : p ≥ 2 := Nat.Prime.two_le hp
        have h4 : p / n ≥ 0 := by 
          apply Nat.zero_le
        have h5 : n + p / n ≥ 1 := by 
          omega
        omega
      have h3 : n + p / n = 0 := by 
        omega
      omega
    · -- Assume (n = 1 ∧ p = 3) ∨ (n = 3 ∧ p = 3), prove m^2 = n + p / n
      intro h2
      exfalso 
      tauto