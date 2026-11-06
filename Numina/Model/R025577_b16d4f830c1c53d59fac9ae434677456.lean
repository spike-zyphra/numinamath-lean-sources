import Mathlib

theorem inequalities_175861 : Set.ncard {(x, y) : ℤ × ℤ | abs (x - 30) + abs (y - 10) < 100} = 19801 := by 
  have h2 : {(x, y) : ℤ × ℤ | abs (x - 30) + abs (y - 10) < 100} = Finset.filter (fun s : ℤ × ℤ => abs (s.1 - 30) + abs (s.2 - 10) < 100) (Finset.Icc (-70 : ℤ) (130 : ℤ) ×ˢ Finset.Icc (-90 : ℤ) (110 : ℤ)) := by
    ext ⟨x, y⟩
    simp 
    intro h
    have h2 : x ≥ -70 := by 
      cases' abs_cases (x - 30) with h3 h3 <;> 
        cases' abs_cases (y - 10) with h4 h4 <;> 
          omega
    have h3 : x ≤ 130 := by 
      cases' abs_cases (x - 30) with h3 h3 <;> 
        cases' abs_cases (y - 10) with h4 h4 <;> 
          omega
    have h4 : y ≥ -90 := by 
      cases' abs_cases (x - 30) with h3 h3 <;> 
        cases' abs_cases (y - 10) with h4 h4 <;> 
          omega
    have h5 : y ≤ 110 := by 
      cases' abs_cases (x - 30) with h3 h3 <;> 
        cases' abs_cases (y - 10) with h4 h4 <;> 
          omega
    tauto
  rw [h2]
  rw [Set.ncard_coe_Finset]
  native_decide