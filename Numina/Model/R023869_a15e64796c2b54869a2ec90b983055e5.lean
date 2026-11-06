import Mathlib

theorem number_theory_5908 :
    (∑ a in (Finset.Icc 1 2022).filter (fun a => 3^a ≡ 12 [MOD 15]), a) / ((Finset.Icc 1 2022).filter (fun a => 3^a ≡ 12 [MOD 15])).card = 1011 := by 
  native_decide