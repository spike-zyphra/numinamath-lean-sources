import Mathlib

theorem algebra_204672 :
    {(m, n) : ℤ × ℤ | m * n ≥ 0 ∧ m^3 + n^3 + 99 * m * n = 33^3}.ncard = 35 := by
  have h1 : {(m, n) : ℤ × ℤ | m * n ≥ 0 ∧ m^3 + n^3 + 99 * m * n = 33^3} = Finset.filter (λ p => p.1 * p.2 ≥ 0 ∧ p.1^3 + p.2^3 + 99 * p.1 * p.2 = 33^3) (Finset.Icc (-66 : ℤ) 66 ×ˢ Finset.Icc (-66 : ℤ) 66) := by
    ext ⟨m, n⟩
    simp
    intro h1 h2
    have h3 : m ≤ 66 := by
      nlinarith [sq_nonneg (m + n + 66), sq_nonneg (m - n), sq_nonneg (m + 66), sq_nonneg (n + 66),
        sq_nonneg (m - 33), sq_nonneg (n - 33), sq_nonneg (m + n + 66), sq_nonneg (m - n)]
    have h4 : m ≥ -66 := by
      nlinarith [sq_nonneg (m + n + 66), sq_nonneg (m - n), sq_nonneg (m - 33), sq_nonneg (n - 33),
        sq_nonneg (m + 66), sq_nonneg (n + 66), sq_nonneg (m - n), sq_nonneg (m + n - 66)]
    have h5 : n ≤ 66 := by
      nlinarith [sq_nonneg (m + n + 66), sq_nonneg (m - n), sq_nonneg (m - 33), sq_nonneg (n - 33),
        sq_nonneg (m + 66), sq_nonneg (n + 66), sq_nonneg (m - n), sq_nonneg (m + n - 66)]
    have h6 : n ≥ -66 := by
      nlinarith [sq_nonneg (m + n + 66), sq_nonneg (m - n), sq_nonneg (m - 33), sq_nonneg (n - 33),
        sq_nonneg (m + 66), sq_nonneg (n + 66), sq_nonneg (m - n), sq_nonneg (m + n - 66)]
    tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide