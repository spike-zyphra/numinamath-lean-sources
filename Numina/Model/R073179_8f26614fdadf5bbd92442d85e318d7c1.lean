import Mathlib

theorem algebra_2049 (S J : ℤ) (hS : S = ∑ i in (Finset.Icc 2 500).filter Even, i)
    (hJ : J = ∑ i in (Finset.Icc 1 250), i) : S / J = 2 := by 
  have hS_val : S = 62750 := by 
    rw [hS]
    native_decide
  have hJ_val : J = 31375 := by 
    rw [hJ]
    native_decide
  rw [hS_val, hJ_val]
  norm_num