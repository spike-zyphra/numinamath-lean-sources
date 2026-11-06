import Mathlib

theorem inequalities_4951 :
    Set.ncard {x : ℕ | (59 : ℤ) - 7 * x > -33} = 14 := by
  have h1 : {x : ℕ | (59 : ℤ) - 7 * x > -33} = Finset.range 14 := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  simp