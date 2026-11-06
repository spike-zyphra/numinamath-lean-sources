import Mathlib

def solution_set : Set ℕ := {n : ℕ | 10 ≤ n ∧ n ≤ 99 ∧ 37 ∣ (6 ^ n : ℤ) - 1}

theorem number_theory_4240 :
    ∑ᶠ n ∈ solution_set, n = 1188 := by 
  have h1 : solution_set = Finset.filter (fun (n : ℕ) => 10 ≤ n ∧ n ≤ 99 ∧ 37 ∣ (6 ^ n : ℤ) - 1) (Finset.Icc (0 : ℕ) 99) := by
    ext n
    simp [solution_set]
    omega
  rw [h1]
  rw [finsum_mem_coe_finset]
  native_decide