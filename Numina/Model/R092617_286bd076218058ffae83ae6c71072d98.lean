import Mathlib

theorem number_theory_233895 :
    {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n = 34 * (Nat.digits 10 n).sum}.encard = 4 := by 
  have h : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n = 34 * (Nat.digits 10 n).sum} = 
    (Finset.Icc 100 999).filter (fun n => n = 34 * (Nat.digits 10 n).sum) := by 
    ext n
    simp
  rw [h]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> native_decide