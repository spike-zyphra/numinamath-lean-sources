import Mathlib

theorem number_theory_192341 :
    Set.ncard {n : ℕ | n > 7777 ∧ (Nat.digits 10 n).sum = 32 ∧ n < 10000} = 31 := by
  have h1 : {n : ℕ | n > 7777 ∧ (Nat.digits 10 n).sum = 32 ∧ n < 10000} = Finset.filter (fun n => n > 7777 ∧ (Nat.digits 10 n).sum = 32 ∧ n < 10000) (Finset.Icc 7778 9999) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide