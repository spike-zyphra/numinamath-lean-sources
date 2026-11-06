import Mathlib

theorem number_theory_217260 :
    {(m, n) : ℤ × ℤ | m * n ≥ 0 ∧ m ^ 3 + n ^ 3 + 99 * m * n = 33 ^ 3}.encard = 35 := by
  have h1 : {(m, n) : ℤ × ℤ | m * n ≥ 0 ∧ m ^ 3 + n ^ 3 + 99 * m * n = 33 ^ 3} = Finset.filter (fun p : ℤ × ℤ => p.1 * p.2 ≥ 0 ∧ p.1 ^ 3 + p.2 ^ 3 + 99 * p.1 * p.2 = 33 ^ 3) (Finset.Icc (-33 : ℤ) 66 ×ˢ Finset.Icc (-33 : ℤ) 66) := by
    ext ⟨m, n⟩
    simp
    intro h1 h2
    have h3 : m ≤ 66 := by
      nlinarith [sq_nonneg (m - 66), sq_nonneg (n - 66), sq_nonneg (m - n), sq_nonneg (m + n - 33), sq_nonneg (m - 33), sq_nonneg (n - 33)]
    have h4 : m ≥ -33 := by
      nlinarith [sq_nonneg (m + 33), sq_nonneg (n + 33), sq_nonneg (m - n), sq_nonneg (m + n + 33), sq_nonneg (m + 33), sq_nonneg (n + 33)]
    have h5 : n ≤ 66 := by
      nlinarith [sq_nonneg (m - 66), sq_nonneg (n - 66), sq_nonneg (m - n), sq_nonneg (m + n - 33), sq_nonneg (m - 33), sq_nonneg (n - 33)]
    have h6 : n ≥ -33 := by
      nlinarith [sq_nonneg (m + 33), sq_nonneg (n + 33), sq_nonneg (m - n), sq_nonneg (m + n + 33), sq_nonneg (m + 33), sq_nonneg (n + 33)]
    simp [Finset.mem_Icc] at *
    tauto
  rw [h1] at *
  rw [Set.encard_coe_eq_coe_finsetCard] at *
  native_decide