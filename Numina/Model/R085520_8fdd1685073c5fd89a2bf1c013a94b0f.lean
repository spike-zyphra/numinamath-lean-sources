import Mathlib

theorem algebra_250967 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 10 n).sum = 10)
    (h₂ : (Nat.digits 10 n)[1]! = (Nat.digits 10 n)[0]! + (Nat.digits 10 n)[2]!)
    (h₃ : 100 * (Nat.digits 10 n)[2]! + 10 * (Nat.digits 10 n)[0]! + (Nat.digits 10 n)[1]! =
    n - 9) :
    n = 154 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> norm_num at h₁ h₂ h₃ ⊢ <;> try trivial
  <;> try omega