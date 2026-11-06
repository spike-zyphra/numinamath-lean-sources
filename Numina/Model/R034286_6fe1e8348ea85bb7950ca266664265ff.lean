import Mathlib

theorem inequalities_115658 :
    {(x, y) : ℤ × ℤ | abs x + abs y < 10}.ncard = 181 := by 
  have h1 : {(x, y) : ℤ × ℤ | abs x + abs y < 10} = Finset.filter (fun p : ℤ × ℤ => abs p.1 + abs p.2 < 10) (Finset.Icc (-9 : ℤ) 9 ×ˢ Finset.Icc (-9 : ℤ) 9) := by
    ext ⟨x, y⟩ 
    simp 
    intro h 
    have h2 : x ≥ -9 := by
      cases' abs_cases x with h1 h1 <;> cases' abs_cases y with h2 h2 <;> omega
    have h3 : x ≤ 9 := by 
      cases' abs_cases x with h1 h1 <;> cases' abs_cases y with h2 h2 <;> omega 
    have h4 : y ≥ -9 := by 
      cases' abs_cases x with h1 h1 <;> cases' abs_cases y with h2 h2 <;> omega 
    have h5 : y ≤ 9 := by 
      cases' abs_cases x with h1 h1 <;> cases' abs_cases y with h2 h2 <;> omega 
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide