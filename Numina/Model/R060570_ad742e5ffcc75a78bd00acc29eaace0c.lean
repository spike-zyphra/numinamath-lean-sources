import Mathlib

theorem number_theory_5348 : {n : ℕ | 0 < n ∧ n ≤ 2017 ∧ Nat.gcd (11 * n + 20) (5 * n + 3) = 1}.encard = 1987 := by
  have h1 : {n : ℕ | 0 < n ∧ n ≤ 2017 ∧ Nat.gcd (11 * n + 20) (5 * n + 3) = 1} = 
    Finset.filter (fun n => 0 < n ∧ n ≤ 2017 ∧ Nat.gcd (11 * n + 20) (5 * n + 3) = 1) (Finset.Icc 0 2017) := by
    ext n
    simp
    <;> omega 
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide