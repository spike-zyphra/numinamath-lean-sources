import Mathlib

theorem algebra_172757 :
    {(x, y) : ℤ × ℤ | x ^ 2 + y ^ 2 < 2019 ∧ x ^ 2 + min x y = y ^ 2 + max x y}.ncard = 127 := by
  have h1 : {(x, y) : ℤ × ℤ | x ^ 2 + y ^ 2 < 2019 ∧ x ^ 2 + min x y = y ^ 2 + max x y} = Finset.filter (fun p : ℤ × ℤ => p.1 ^ 2 + p.2 ^ 2 < 2019 ∧ p.1 ^ 2 + min p.1 p.2 = p.2 ^ 2 + max p.1 p.2) (Finset.Icc (-44 : ℤ) 44 ×ˢ Finset.Icc (-44 : ℤ) 44) := by
    ext ⟨x, y⟩
    simp
    intro h1 h2
    have h3 : x ≥ -44 := by
      nlinarith [sq_nonneg (x + 44), sq_nonneg (y + 44)]
    have h4 : x ≤ 44 := by
      nlinarith [sq_nonneg (x - 44), sq_nonneg (y - 44)]
    have h5 : y ≥ -44 := by
      nlinarith [sq_nonneg (x + 44), sq_nonneg (y + 44)]
    have h6 : y ≤ 44 := by
      nlinarith [sq_nonneg (x - 44), sq_nonneg (y - 44)]
    tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide