import Mathlib

theorem number_theory_232361 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) :
    11 ∣ n * 100 + (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h10, h99⟩
  interval_cases n <;> native_decide