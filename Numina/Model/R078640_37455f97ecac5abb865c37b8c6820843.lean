import Mathlib

theorem number_theory_108651 (n : ℕ) (h₀ : n > 0) (h₁ : n ≤ 2005 - 17) :
    ∃ m ∈ Finset.Icc n (n + 17), (Nat.digits 10 m).sum ∣ m := by
  have h2 : n ≤ 1988 := by
    omega
  interval_cases n <;> native_decide