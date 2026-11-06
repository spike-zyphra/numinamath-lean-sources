import Mathlib

def sumdigits (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_4145 :
    Set.ncard {n | 0 < n ∧ n ≤ 10000 ∧ sumdigits n = 19} = 660 := by
  have h1 : {n | 0 < n ∧ n ≤ 10000 ∧ sumdigits n = 19} = Finset.filter (fun n => 0 < n ∧ n ≤ 10000 ∧ sumdigits n = 19) (Finset.Icc 0 10000) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide