import Mathlib

open Real
open scoped BigOperators

theorem inequalities_181919 :
  Set.ncard {p : ℤ × ℤ | abs (p.1 - 30) + abs (p.2 - 10) < 100} = 19801 := by
  have h1 : {p : ℤ × ℤ | abs (p.1 - 30) + abs (p.2 - 10) < 100} = Finset.filter (fun p : ℤ × ℤ => abs (p.1 - 30) + abs (p.2 - 10) < 100) (Finset.Icc (-70 : ℤ) (129 : ℤ) ×ˢ Finset.Icc (-90 : ℤ) (109 : ℤ)) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h2 : abs (x - 30) + abs (y - 10) < 100 := h
    have h3 : x ≥ -70 := by 
      cases' abs_cases (x - 30) with h1 h1 <;> 
      cases' abs_cases (y - 10) with h2 h2 <;> omega
    have h4 : x ≤ 129 := by 
      cases' abs_cases (x - 30) with h1 h1 <;> 
      cases' abs_cases (y - 10) with h2 h2 <;> omega
    have h5 : y ≥ -90 := by 
      cases' abs_cases (x - 30) with h1 h1 <;> 
      cases' abs_cases (y - 10) with h2 h2 <;> omega
    have h6 : y ≤ 109 := by 
      cases' abs_cases (x - 30) with h1 h1 <;> 
      cases' abs_cases (y - 10) with h2 h2 <;> omega
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide