import Mathlib

theorem number_theory_13326 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 = 325^2} = 60 := by 
  have h1 : {p : ℤ × ℤ | p.1^2 + p.2^2 = 325^2} = Finset.filter (λ p => p.1^2 + p.2^2 = 325^2) (Finset.Icc (-1000 : ℤ) 1000 ×ˢ Finset.Icc (-1000 : ℤ) 1000) := by
    ext ⟨x, y⟩
    simp
    intro h_eq
    have hx1 : x ^ 2 ≤ 325^2 := by nlinarith [sq_nonneg (y : ℤ)]
    have hy1 : y ^ 2 ≤ 325^2 := by nlinarith [sq_nonneg (x : ℤ)]
    have hx2 : x ≤ 325 := by nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), h_eq]
    have hy2 : y ≤ 325 := by nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), h_eq]
    have hx3 : x ≥ -325 := by nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), h_eq]
    have hy3 : y ≥ -325 := by nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), h_eq]
    have hx4 : x ≤ 1000 := by omega
    have hy4 : y ≤ 1000 := by omega
    have hx5 : x ≥ -1000 := by omega
    have hy5 : y ≥ -1000 := by omega
    tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide