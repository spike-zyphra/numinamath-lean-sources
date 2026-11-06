import Mathlib

theorem number_theory_8365 :
    ∀ n : ℕ, ∃ a b c : ℕ,
      a > n ∧ b > n ∧ c > n ∧
      (Nat.primeFactors (a ^ 2 + 1)).max =
        (Nat.primeFactors (b ^ 2 + 1)).max ∧
      (Nat.primeFactors (b ^ 2 + 1)).max =
        (Nat.primeFactors (c ^ 2 + 1)).max := by 
  intro n
  refine' ⟨n+1, n+1, n+1, by nlinarith, by nlinarith, by nlinarith, rfl, rfl⟩
  all_goals simp
  all_goals tauto