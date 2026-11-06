import Mathlib

theorem number_theory_233207 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    11 ∣ n * 1000 + (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀, h₁⟩ 
  interval_cases n <;> native_decide