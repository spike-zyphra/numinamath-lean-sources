import Mathlib

theorem number_theory_230804 :
    Set.ncard {n : ℕ | 100 ≤ n ∧ n < 300 ∧ ∀ d ∈ Nat.digits 10 n, Odd d} = 25 := by

  have : {n : ℕ | 100 ≤ n ∧ n < 300 ∧ ∀ d ∈ Nat.digits 10 n, Odd d} = Finset.filter (fun n => 100 ≤ n ∧ n < 300 ∧ ∀ d ∈ Nat.digits 10 n, Odd d) (Finset.Icc 0 300) := by 
    ext n
    simp
    omega

  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide