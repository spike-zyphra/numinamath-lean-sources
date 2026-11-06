import Mathlib

theorem calculus_14433 :
    {(x, y, z) : ℤ × ℤ × ℤ | (x ^ 2 + y ^ 2 + z ^ 2) = 3 ^ 2}.ncard = 30 := by
  have h1 : {(x, y, z) : ℤ × ℤ × ℤ | (x ^ 2 + y ^ 2 + z ^ 2) = 3 ^ 2} = Finset.filter (fun p : ℤ × ℤ × ℤ => (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) = 3 ^ 2) (Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3) := by
    ext ⟨x, y, z⟩
    simp
    intro h
    have h1 : x ≤ 3 := by nlinarith
    have h2 : x ≥ -3 := by nlinarith
    have h3 : y ≤ 3 := by nlinarith
    have h4 : y ≥ -3 := by nlinarith
    have h5 : z ≤ 3 := by nlinarith
    have h6 : z ≥ -3 := by nlinarith
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide