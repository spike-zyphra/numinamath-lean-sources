import Mathlib

theorem number_theory_225953 : ∑ᶠ n ∈ {n : ℕ | 1 ≤ n ∧ n ≤ 5000 ∧ 2477 ∣ n^2 + 2475 * n + 2454 + (-1 : ℤ)^n}, n = 9912 := by 
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 5000 ∧ 2477 ∣ n^2 + 2475 * n + 2454 + (-1 : ℤ)^n} = Finset.filter (fun n : ℕ => 1 ≤ n ∧ n ≤ 5000 ∧ 2477 ∣ n^2 + 2475 * n + 2454 + (-1 : ℤ)^n) (Finset.Icc (0 : ℕ) 5000) := by
    ext n
    simp
    <;> omega
  rw [h1] 
  rw [finsum_mem_coe_finset]
  native_decide