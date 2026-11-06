import Mathlib

open Finset Polynomial

lemma f_coeff_n0 : ∀ n, (∏ i ∈ range n, (X + (i + 1))).coeff (n+1) = (0:ℚ) := by
  intro n

  apply coeff_eq_zero_of_natDegree_lt

  rw [natDegree_prod']
  . norm_cast

    have h1: ∀ x ∈ range n, (X + ((x + 1):ℚ[X])).natDegree  = 1 := by
      intro x hx
      norm_cast
      rw [← C_eq_natCast]
      rw [natDegree_X_add_C]

    have h2 : ∑ x ∈ range n, (X + ((x + 1):ℚ[X])).natDegree = n := by
      have := sum_congr rfl h1
      rw [this]
      simp [sum_const]

    norm_cast at h2
    rw [h2]
    omega


  . have h1 : ∀ x ∈ range n, (X + ((x + 1):ℚ[X])).leadingCoeff = 1 := by
      intro x hx
      norm_cast
      rw [← C_eq_natCast]
      rw [leadingCoeff_X_add_C]

    have h2 : ∏ x ∈ range n, (X + ((x + 1):ℚ[X])).leadingCoeff = 1 := by
      have := prod_congr rfl h1
      rw [this]
      simp

    rw [h2]
    norm_num

lemma f_coeff_n1 : ∀ n, (∏ i ∈ range n, (X + (i + 1))).coeff n = (1:ℚ) := by
  intro n

  induction' n with n hn
  . simp
  . rw [prod_range_succ, mul_add]
    simp
    rw [hn]
    simp
    norm_cast
    rw [coeff_mul_natCast]
    simp
    have := f_coeff_n0 (n)
    left
    rw [this]

lemma f_coeff_n2 : ∀ n, (∏ i ∈ range (n + 1), (X + (i + 1))).coeff (n) = (n + 1) * (n + 2) / (2:ℚ) := by
  intro n
  induction' n with n hn
  . simp
  . rw [prod_range_succ, mul_add]
    simp
    rw [hn]

    norm_cast
    rw [coeff_mul_natCast]
    have := f_coeff_n1 (n + 1)
    norm_cast at this
    rw [this]
    simp
    ring_nf

theorem algebra_312331 : ∀ n, (∏ i ∈ range (n + 2), (X + (i + 1))).coeff (n) = (1 + n) * (2 + n) * (3 + n) * (8 + 3 * n) / (24:ℚ):= by
  intro n
  induction' n with n hn
  . rw [prod_range_succ]
    simp
    norm_num

  . rw [prod_range_succ, mul_add]
    simp
    rw [hn]
    norm_cast
    rw [coeff_mul_natCast]
    have := f_coeff_n2 (n + 1)
    norm_cast at this
    rw [this]
    simp
    ring_nf
