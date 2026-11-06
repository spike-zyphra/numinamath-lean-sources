import Mathlib

theorem algebra_12886 :
    {(x, y) : ℤ × ℤ | x^2 + 3 * y^2 + 6 * x - 6 * y = 100}.ncard = 12 := by
  have h1 : {(x, y) : ℤ × ℤ | x^2 + 3 * y^2 + 6 * x - 6 * y = 100} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + 3 * p.2^2 + 6 * p.1 - 6 * p.2 = 100) (Finset.Icc (-13 : ℤ) 7 ×ˢ Finset.Icc (-5 : ℤ) 7) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h2 : x ≥ -13 := by 
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 1)]
    have h3 : x ≤ 7 := by 
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 1)]
    have h4 : y ≥ -5 := by 
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 1)]
    have h5 : y ≤ 7 := by 
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 1)]
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide