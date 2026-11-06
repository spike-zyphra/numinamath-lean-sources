import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_304970 :
  {(x, y) : ℤ × ℤ | 2 * x ≥ 3 * y ∧ 3 * x ≥ 4 * y ∧ 5 * x - 7 * y ≤ 20}.ncard = 231 := by 
  have h1 : {(x, y) : ℤ × ℤ | 2 * x ≥ 3 * y ∧ 3 * x ≥ 4 * y ∧ 5 * x - 7 * y ≤ 20} = Finset.filter (fun p : ℤ × ℤ => 2 * p.1 ≥ 3 * p.2 ∧ 3 * p.1 ≥ 4 * p.2 ∧ 5 * p.1 - 7 * p.2 ≤ 20) (Finset.Icc (-80 : ℤ) 60 ×ˢ Finset.Icc (-80 : ℤ) 60) := by
    ext ⟨x, y⟩
    simp 
    intro h1 h2 h3 
    have h4 : x ≤ 60 := by 
      omega 
    have h5 : x ≥ -80 := by 
      omega 
    have h6 : y ≤ 60 := by 
      omega 
    have h7 : y ≥ -80 := by 
      omega 
    norm_num 
    all_goals omega 
  rw [h1] 
  rw [Set.ncard_coe_Finset] 
  native_decide