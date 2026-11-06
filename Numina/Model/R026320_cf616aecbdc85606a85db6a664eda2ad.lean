import Mathlib

theorem inequalities_192563 : {p : ℤ × ℤ | |p.1| + |p.2| < 100}.ncard = 19801 := by
  have h1 : {p : ℤ × ℤ | |p.1| + |p.2| < 100} = Finset.filter (fun p : ℤ × ℤ => |p.1| + |p.2| < 100) (Finset.Icc (-100 : ℤ) 100 ×ˢ Finset.Icc (-100 : ℤ) 100) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h1 : |x| < 100 := by
      linarith [abs_nonneg y, abs_nonneg x]
    have h2 : |y| < 100 := by
      linarith [abs_nonneg x, abs_nonneg y]
    have h3 : x ≥ -100 := by 
      cases' abs_lt.mp h1 with h4 h5
      omega
    have h4 : x ≤ 100 := by 
      cases' abs_lt.mp h1 with h4 h5
      omega
    have h5 : y ≥ -100 := by 
      cases' abs_lt.mp h2 with h6 h7
      omega
    have h6 : y ≤ 100 := by 
      cases' abs_lt.mp h2 with h6 h7
      omega
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide