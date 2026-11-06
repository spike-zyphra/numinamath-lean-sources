import Mathlib

theorem number_theory_250956 (n : ℕ) (h₀ : n = ∑ i ∈ Finset.range 199, (Nat.ofDigits 10 (List.replicate (i + 1) 9))) :
    (Nat.digits 10 n).sum = 207 := by 
  rw [h₀]
  native_decide