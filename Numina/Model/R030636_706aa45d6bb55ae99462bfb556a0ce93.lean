import Mathlib

open Real
open scoped BigOperators

theorem inequalities_184079 :
  {(x, y) : ℤ × ℤ | |x| + |y| ≤ 100}.ncard = 20201 := by
  have h1 : {(x, y) : ℤ × ℤ | |x| + |y| ≤ 100} = Finset.filter (fun s : ℤ × ℤ => |s.1| + |s.2| ≤ 100) (Finset.Icc (-100 : ℤ) 100 ×ˢ Finset.Icc (-100 : ℤ) 100) := by
    ext ⟨x, y⟩
    simp
    intro h 
    have h2 : x ≥ -100 := by 
      cases' abs_cases x with h3 h3 <;> 
      cases' abs_cases y with h4 h4 <;> 
      omega
    have h3 : x ≤ 100 := by 
      cases' abs_cases x with h4 h4 <;> 
      cases' abs_cases y with h5 h5 <;> 
      omega
    have h4 : y ≥ -100 := by
      cases' abs_cases x with h5 h5 <;> 
      cases' abs_cases y with h6 h6 <;> 
      omega
    have h5 : y ≤ 100 := by
      cases' abs_cases x with h6 h6 <;> 
      cases' abs_cases y with h7 h7 <;> 
      omega
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide