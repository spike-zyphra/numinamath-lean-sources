import Mathlib

theorem number_theory_133335 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 100 ∧ n.divisors.card^2 = n} = 2 := by
  have h : {n : ℕ | n ∈ Finset.Icc 1 100 ∧ n.divisors.card^2 = n} = Finset.filter (fun n => n.divisors.card^2 = n) (Finset.Icc 1 100) := by
    ext n
    simp
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide