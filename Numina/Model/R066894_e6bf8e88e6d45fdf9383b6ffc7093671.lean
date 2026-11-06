import Mathlib

theorem number_theory_164837 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : (Nat.digits 10 n).sum = 10)
    (h₂ : (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)) + 1) = 2 * n) :
    n = 37 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h₁ h₂ <;> all_goals trivial