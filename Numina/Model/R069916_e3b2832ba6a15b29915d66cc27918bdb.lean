import Mathlib

theorem number_theory_312654 :
    ∑ᶠ n ∈ {n : ℕ | 0 < n ∧ n < 100 ∧ 15 ∣ 5 * n ^ 2 + 3 * n - 5}, n = 635 := by
  have h1 : {n : ℕ | 0 < n ∧ n < 100 ∧ 15 ∣ 5 * n ^ 2 + 3 * n - 5} = Finset.filter (fun n => 0 < n ∧ n < 100 ∧ 15 ∣ 5 * n ^ 2 + 3 * n - 5) (Finset.Icc 0 100) := by
    ext n 
    simp 
    <;> omega 
  rw [h1]
  rw [finsum_mem_coe_finset]
  native_decide