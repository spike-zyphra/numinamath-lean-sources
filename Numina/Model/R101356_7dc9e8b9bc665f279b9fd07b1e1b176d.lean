import Mathlib

def isSupreme (n : ℕ) := (Nat.digits 10 n).sum = 9

theorem number_theory_3860 :
    Set.ncard {n | n < 2023 ∧ isSupreme n} = 102 := by
  have h1 : {n | n < 2023 ∧ isSupreme n} = Finset.filter (fun n => (Nat.digits 10 n).sum = 9) (Finset.Iio 2023) := by
    ext n
    simp [isSupreme, Finset.mem_filter, Finset.mem_Iio]
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide