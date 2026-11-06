import Mathlib

theorem number_theory_237159 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : 11 ∣ n)
    (h₂ : (n / 11) = (Nat.digits 10 n).headI ^ 2 + (Nat.digits 10 n).tail.headI ^ 2 + (Nat.digits 10 n).tail.tail.headI ^ 2) :
    n = 803 ∨ n = 550 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀l, h₀u⟩
  interval_cases n <;> norm_num at h₁ h₂ <;> omega