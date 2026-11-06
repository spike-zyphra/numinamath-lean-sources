import Mathlib

def isLucky (m : ℕ) : Prop := m < 2012 ∧ 6 ∣ m ∧ 6 ∣ (Nat.digits 10 m).sum

theorem number_theory_319789 :
    Set.ncard {m | isLucky m} = 168 := by
  have h1 : {m | isLucky m} = Finset.filter (fun m => 6 ∣ m ∧ 6 ∣ (Nat.digits 10 m).sum) (Finset.Iio 2012) := by
    ext m
    simp [isLucky, Finset.mem_filter, Finset.mem_Iio]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide