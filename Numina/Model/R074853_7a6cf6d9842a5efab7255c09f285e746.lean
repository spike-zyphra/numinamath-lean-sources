import Mathlib

theorem number_theory_295576 (n : ℕ) (h₀ : n ≤ 2016 - 17) :
    ∃ m ∈ Finset.Icc n (n + 17), (Nat.digits 10 m).sum ∣ m := by 
        have h1 : n ≤ 2016 - 17 := h₀
        have h2 : n + 17 ≤ 2016 := by omega
        interval_cases n <;> native_decide