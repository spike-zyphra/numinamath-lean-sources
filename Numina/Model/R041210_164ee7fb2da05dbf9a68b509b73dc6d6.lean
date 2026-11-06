import Mathlib

def R : ℕ → ℕ
| n => ∑ i ∈ Finset.Icc 2 10, n % i

theorem number_theory_94998 :
    Set.ncard {n | n ∈ Finset.Icc 10 99 ∧ R n = R (n + 1)} = 2 := by

  have : {n | n ∈ Finset.Icc 10 99 ∧ R n = R (n + 1)} = 
    Finset.filter (fun n => R n = R (n + 1)) (Finset.Icc 10 99) := by
    ext n
    simp

  rw [this]

  rw [Set.ncard_coe_Finset]

  native_decide