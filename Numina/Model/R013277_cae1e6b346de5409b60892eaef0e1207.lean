import Mathlib

def is_susanian (n : ℕ) : Prop := (Nat.digits 10 n).sum = 9 ∧ 15 ∣ n

theorem number_theory_6196 :
    Set.ncard {n | n < 500 ∧ is_susanian n} = 10 := by 
  have h1 : {n | n < 500 ∧ is_susanian n} = 
    Finset.filter (fun n => (Nat.digits 10 n).sum = 9 ∧ 15 ∣ n) (Finset.Iio 500) := by
    ext n
    simp [is_susanian, Finset.mem_filter, Finset.mem_Iio]
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide