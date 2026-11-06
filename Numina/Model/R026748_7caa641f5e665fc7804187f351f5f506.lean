import Mathlib

theorem algebra_277039 : {(x, y) : ℤ × ℤ | x ≥ 0 ∧ 2 * x ^ 2 - 2 * x * y + y ^ 2 = 289}.encard = 7 := by 
  have h1 : {(x, y) : ℤ × ℤ | x ≥ 0 ∧ 2 * x ^ 2 - 2 * x * y + y ^ 2 = 289} = Finset.filter (fun p : ℤ × ℤ => p.1 ≥ 0 ∧ 2 * p.1 ^ 2 - 2 * p.1 * p.2 + p.2 ^ 2 = 289) (Finset.Icc (0 : ℤ) 17 ×ˢ Finset.Icc (-27 : ℤ) 31) := by
    ext ⟨x, y⟩
    simp
    intro h1 h2
    have h3 : x ≤ 17 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - 17), sq_nonneg (x), sq_nonneg (y - x)]
    have h4 : y ≤ 31 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - 17), sq_nonneg (x), sq_nonneg (y - x)]
    have h5 : x ≥ 0 := by linarith
    have h6 : y ≥ -27 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y + 27), sq_nonneg (x), sq_nonneg (y - x)]
    omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide