import Mathlib

theorem inequalities_6107 :
    Set.ncard {p : ℤ × ℤ | abs p.1 + abs p.2 < 12} = 265 := by
  have h1 : {p : ℤ × ℤ | abs p.1 + abs p.2 < 12} = Finset.filter (fun p : ℤ × ℤ => abs p.1 + abs p.2 < 12) (Finset.Icc (-11 : ℤ) 11 ×ˢ Finset.Icc (-11 : ℤ) 11) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h2 : abs x ≤ 11 := by
      cases' abs_cases x with h3 h3 <;> cases' abs_cases y with h4 h4
      all_goals
        omega
    have h3 : abs y ≤ 11 := by
      cases' abs_cases x with h3 h3 <;> cases' abs_cases y with h4 h4
      all_goals
        omega
    have h4 : -11 ≤ x := by
      cases' abs_cases x with h3 h3
      · omega
      · omega
    have h5 : x ≤ 11 := by
      cases' abs_cases x with h3 h3
      · omega
      · omega
    have h6 : -11 ≤ y := by
      cases' abs_cases y with h4 h4
      · omega
      · omega
    have h7 : y ≤ 11 := by
      cases' abs_cases y with h4 h4
      · omega
      · omega
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide