import Mathlib

theorem algebra_150777 (S : Finset ℕ) (hS : S = Finset.Icc 1 2016) :
    1000 ∈ S := by 
  rw [hS]
  exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩