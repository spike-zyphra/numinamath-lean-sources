import Mathlib

theorem number_theory_275449 : {n : ℕ | 2 ≤ n ∧ n ≤ 80 ∧ (n - 1) * n * (n + 1) % 8 = 0}.encard = 49 := by
  have h1 : {n : ℕ | 2 ≤ n ∧ n ≤ 80 ∧ (n - 1) * n * (n + 1) % 8 = 0} = 
          Finset.filter (fun (n : ℕ) => 2 ≤ n ∧ n ≤ 80 ∧ (n - 1) * n * (n + 1) % 8 = 0) (Finset.Icc (0 : ℕ) 80) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide