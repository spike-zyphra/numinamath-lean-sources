import Mathlib

theorem algebra_16265 :
    Set.ncard {n : ℕ | 100 ≤ n ∧ n ≤ 150 ∧ n / 100 < (n - 100) / 10 ∧ (n - 100) / 10 < n % 10} = 18 := by
  have h1 : {n : ℕ | 100 ≤ n ∧ n ≤ 150 ∧ n / 100 < (n - 100) / 10 ∧ (n - 100) / 10 < n % 10} = Finset.filter (fun n => 100 ≤ n ∧ n ≤ 150 ∧ n / 100 < (n - 100) / 10 ∧ (n - 100) / 10 < n % 10) (Finset.Icc 100 150) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide