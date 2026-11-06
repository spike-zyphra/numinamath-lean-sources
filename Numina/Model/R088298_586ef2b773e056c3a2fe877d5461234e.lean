import Mathlib

theorem number_theory_309572 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 95 ∧ Odd (n ^ 2 / 10) ∧ n ^ 2 % 10 ≠ 0} = 19 := by
  have : {n : ℕ | n ∈ Finset.Icc 1 95 ∧ Odd (n ^ 2 / 10) ∧ n ^ 2 % 10 ≠ 0} = Finset.filter (fun n => Odd (n ^ 2 / 10) ∧ n ^ 2 % 10 ≠ 0) (Finset.Icc 1 95) := by
    ext n
    simp
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide