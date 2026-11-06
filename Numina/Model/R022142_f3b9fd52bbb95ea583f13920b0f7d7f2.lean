import Mathlib

open Real Int Nat Set
open scoped BigOperators

theorem inequalities_302301 :
  {x : ℤ | abs (x - 2006) + abs x ≤ 9999}.ncard = 9999 := by
  have h1 : {x : ℤ | abs (x - 2006) + abs x ≤ 9999} = Finset.filter (fun (x : ℤ) => abs (x - 2006) + abs x ≤ 9999) (Finset.Icc (-3996 : ℤ) (6002 : ℤ)) := by 
    ext x 
    simp
    intro h 
    have h2 : x ≥ -3996 := by 
      cases' abs_cases (x - 2006) with h1 h1 <;> 
      cases' abs_cases x with h2 h2 <;> 
      omega
    have h3 : x ≤ 6002 := by 
      cases' abs_cases (x - 2006) with h1 h1 <;> 
      cases' abs_cases x with h2 h2 <;> 
      omega
    omega 
  rw [h1] 
  rw [Set.ncard_coe_Finset]
  native_decide