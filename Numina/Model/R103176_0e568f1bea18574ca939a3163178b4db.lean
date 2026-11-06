import Mathlib

theorem number_theory_180381 :
    Set.ncard {n : ℕ | n ≤ 2019 ∧ ¬(n % 6 = 0) ∧ ¬(n % 9 = 0) ∧ ¬(n % 15 = 0)} = 1526 := by
  have h1 : {n : ℕ | n ≤ 2019 ∧ ¬(n % 6 = 0) ∧ ¬(n % 9 = 0) ∧ ¬(n % 15 = 0)} = Finset.filter (fun n => ¬(n % 6 = 0) ∧ ¬(n % 9 = 0) ∧ ¬(n % 15 = 0)) (Finset.Iic (2019)) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide