import Mathlib

theorem algebra_181171 :
    {(x, y, z) : ℤ × ℤ × ℤ | x^2 + y^2 + z^2 - 4 * x + 12 * y - 14 * z - 57 = 0}.ncard = 192 := by
  have h1 : {(x, y, z) : ℤ × ℤ × ℤ | x^2 + y^2 + z^2 - 4 * x + 12 * y - 14 * z - 57 = 0} = Finset.filter (fun s : ℤ × ℤ × ℤ => 
    let (x, y, z) := s
    x^2 + y^2 + z^2 - 4 * x + 12 * y - 14 * z - 57 = 0) (Finset.Icc (-25 : ℤ) 31 ×ˢ Finset.Icc (-32 : ℤ) 20 ×ˢ Finset.Icc (-24 : ℤ) 25) := by
    ext ⟨x, y, z⟩
    simp
    intro h_eq
    have h2 : x ≤ 31 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 6), sq_nonneg (z - 7)]
    have h3 : x ≥ -25 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 6), sq_nonneg (z - 7)]
    have h4 : y ≤ 20 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 6), sq_nonneg (z - 7)]
    have h5 : y ≥ -32 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 6), sq_nonneg (z - 7)]
    have h6 : z ≤ 25 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 6), sq_nonneg (z - 7)]
    have h7 : z ≥ -24 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 6), sq_nonneg (z - 7)]
    simp [Finset.mem_Icc, h2, h3, h4, h5, h6, h7]
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide