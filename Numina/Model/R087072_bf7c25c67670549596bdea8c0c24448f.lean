import Mathlib

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_75657 :
    Set.ncard {n | n ∈ Finset.Icc 100 999 ∧ S (S n) = 2} = 100 := by
  have h1 : {n | n ∈ Finset.Icc 100 999 ∧ S (S n) = 2} = Finset.filter (fun n => S (S n) = 2) (Finset.Icc 100 999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide