import Mathlib

theorem inequalities_176505 :
    {(x1, x2, x3) : ℤ × ℤ × ℤ | abs (5 - x1 - x2) + abs (5 + x1 - x2) +
      abs (5 + x2 + x3) + abs (5 + x2 - x3) = 20}.ncard = 891 := by 
  have h1 : {(x1, x2, x3) : ℤ × ℤ × ℤ | abs (5 - x1 - x2) + abs (5 + x1 - x2) +
      abs (5 + x2 + x3) + abs (5 + x2 - x3) = 20} = Finset.filter (fun s : ℤ × ℤ × ℤ => 
      abs (5 - s.1 - s.2.1) + abs (5 + s.1 - s.2.1) + abs (5 + s.2.1 + s.2.2) + abs (5 + s.2.1 - s.2.2) = 20) (Finset.Icc (-10 : ℤ) 20 ×ˢ Finset.Icc (-10 : ℤ) 20 ×ˢ Finset.Icc (-10 : ℤ) 20) := by
    ext ⟨x1, x2, x3⟩
    simp
    intro h
    have h2 : x1 ≤ 20 := by
      cases' abs_cases (5 - x1 - x2) with h11 h11 <;> 
        cases' abs_cases (5 + x1 - x2) with h22 h22 <;> 
          cases' abs_cases (5 + x2 + x3) with h33 h33 <;> 
            cases' abs_cases (5 + x2 - x3) with h44 h44 <;> 
              omega
    have h3 : x1 ≥ -10 := by
      cases' abs_cases (5 - x1 - x2) with h11 h11 <;> 
        cases' abs_cases (5 + x1 - x2) with h22 h22 <;> 
          cases' abs_cases (5 + x2 + x3) with h33 h33 <;> 
            cases' abs_cases (5 + x2 - x3) with h44 h44 <;> 
              omega
    have h4 : x2 ≤ 20 := by
      cases' abs_cases (5 - x1 - x2) with h11 h11 <;> 
        cases' abs_cases (5 + x1 - x2) with h22 h22 <;> 
          cases' abs_cases (5 + x2 + x3) with h33 h33 <;> 
            cases' abs_cases (5 + x2 - x3) with h44 h44 <;> 
              omega
    have h5 : x2 ≥ -10 := by
      cases' abs_cases (5 - x1 - x2) with h11 h11 <;> 
        cases' abs_cases (5 + x1 - x2) with h22 h22 <;> 
          cases' abs_cases (5 + x2 + x3) with h33 h33 <;> 
            cases' abs_cases (5 + x2 - x3) with h44 h44 <;> 
              omega
    have h6 : x3 ≤ 20 := by
      cases' abs_cases (5 - x1 - x2) with h11 h11 <;> 
        cases' abs_cases (5 + x1 - x2) with h22 h22 <;> 
          cases' abs_cases (5 + x2 + x3) with h33 h33 <;> 
            cases' abs_cases (5 + x2 - x3) with h44 h44 <;> 
              omega
    have h7 : x3 ≥ -10 := by
      cases' abs_cases (5 - x1 - x2) with h11 h11 <;> 
        cases' abs_cases (5 + x1 - x2) with h22 h22 <;> 
          cases' abs_cases (5 + x2 + x3) with h33 h33 <;> 
            cases' abs_cases (5 + x2 - x3) with h44 h44 <;> 
              omega
    tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide