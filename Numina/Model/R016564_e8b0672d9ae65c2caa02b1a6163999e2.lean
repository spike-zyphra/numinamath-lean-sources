import Mathlib

theorem number_theory_175021 :
    Set.ncard {n : ℕ | 0 < n ∧ n % 4 = 0 ∧ (n + 1) % 5 = 0 ∧ (n + 2) % 6 = 0 ∧ n < 2018} = 34 := by
  have h1 : {n : ℕ | 0 < n ∧ n % 4 = 0 ∧ (n + 1) % 5 = 0 ∧ (n + 2) % 6 = 0 ∧ n < 2018} = Finset.filter (fun n => 0 < n ∧ n % 4 = 0 ∧ (n + 1) % 5 = 0 ∧ (n + 2) % 6 = 0 ∧ n < 2018) (Finset.Icc 0 2017) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide