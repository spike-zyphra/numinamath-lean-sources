import Mathlib

theorem number_theory_218734 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1314 2021 ∧ ∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧ d ≠ 4} = 381 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1314 2021 ∧ ∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧ d ≠ 4} = Finset.filter (fun n => ∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧ d ≠ 4) (Finset.Icc 1314 2021) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide