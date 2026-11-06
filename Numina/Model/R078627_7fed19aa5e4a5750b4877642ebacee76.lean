import Mathlib

theorem number_theory_254510 :
    Set.ncard {n : ℕ | 10 ≤ n ∧ n < 100 ∧ (10 * (n % 10) + (n / 10)) > n} = 36 := by
  have h1 : {n : ℕ | 10 ≤ n ∧ n < 100 ∧ (10 * (n % 10) + (n / 10)) > n} = Finset.filter (fun n => 10 ≤ n ∧ n < 100 ∧ (10 * (n % 10) + (n / 10)) > n) (Finset.Icc 0 99) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide