import Mathlib

theorem number_theory_172327 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    99 ∣ (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)) - n) := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁, h₂⟩
  interval_cases n <;> native_decide