import Mathlib

theorem number_theory_172705 :
    ∑ᶠ n ∈ {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ IsSquare (Nat.factorial n * Nat.factorial (n + 1) / 2)}, n = 273 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ IsSquare (Nat.factorial n * Nat.factorial (n + 1) / 2)} = 
    Finset.filter (fun n => 1 ≤ n ∧ n ≤ 100 ∧ IsSquare (Nat.factorial n * Nat.factorial (n + 1) / 2)) (Finset.Icc 0 100) := by
    ext n
    simp
    omega
  rw [h1]
  rw [finsum_mem_coe_finset]
  native_decide