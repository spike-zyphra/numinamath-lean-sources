import Mathlib

theorem number_theory_96388 : ({N | N ∈ (Finset.Icc 1 2020) ∧ N^16 % 5 = 1}.ncard : ℝ) / (Finset.Icc 1 2020).card = (4 : ℝ) / 5 := by
  have h1 : {N | N ∈ (Finset.Icc 1 2020) ∧ N^16 % 5 = 1} = Finset.filter (fun N => N^16 % 5 = 1) (Finset.Icc 1 2020) := by 
    ext N
    simp 
  rw [h1] at *
  rw [Set.ncard_coe_Finset]
  have h2 : (Finset.filter (fun N => N^16 % 5 = 1) (Finset.Icc 1 2020)).card = 1616 := by 
    native_decide 
  have h3 : (Finset.Icc 1 2020).card = 2020 := by 
    native_decide 
  rw [h2, h3]
  norm_num