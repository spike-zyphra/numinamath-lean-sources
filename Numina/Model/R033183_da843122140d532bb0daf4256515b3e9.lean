import Mathlib

open Polynomial

theorem algebra_21487 (P : ℚ[X]) (h : P = (X - 2)^2 * (X + 2)^2) : ∏ᶠ (i : ℕ) (h : P.coeff i ≠ 0), P.coeff i = -128 := by
  have eq1 : P = (X - 2)^2 * (X + 2)^2 := h
  have eq2 : P = X ^ 4 - 8 * X ^ 2 + 16 := by
    rw [eq1]
    ring_nf
  have eq3 : P.coeff 0 = 16 := by 
    rw [eq2]
    norm_num [coeff_eq_zero_of_natDegree_lt]
  have eq4 : P.coeff 1 = (0 : ℚ) := by 
    rw [eq2]
    norm_num [coeff_eq_zero_of_natDegree_lt]
  have eq5 : P.coeff 2 = (-8 : ℚ) := by 
    rw [eq2]
    norm_num [coeff_eq_zero_of_natDegree_lt]
  have eq6 : P.coeff 3 = (0 : ℚ) := by 
    rw [eq2]
    norm_num [coeff_eq_zero_of_natDegree_lt]
  have eq7 : P.coeff 4 = (1 : ℚ) := by 
    rw [eq2]
    norm_num [coeff_eq_zero_of_natDegree_lt]
  -- Show that coefficients higher than 4 are zero.
  have eq8 : ∀ i > 4, P.coeff i = 0 := by
    intro i hi
    rw [eq2]
    have h1 : i > (4 : ℕ) := hi
    have h3 : ((X ^ 4 - 8 * X ^ 2 + 16 : ℚ[X]).natDegree) ≤ 4 := by
        compute_degree!
        all_goals norm_num
    have h4 : i > ((X ^ 4 - 8 * X ^ 2 + 16 : ℚ[X]).natDegree) := by 
      omega
    have h5 : ((X ^ 4 - 8 * X ^ 2 + 16 : ℚ[X]).coeff i) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt 
        omega
    simpa using h5
  -- Show that the set of indices with non-zero coefficients is {0, 2, 4}
  have h1 : {i | P.coeff i ≠ 0} = {0, 2, 4} := by
    ext i 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor 
    · -- Assume P.coeff i ≠ 0 
      intro h_ne 
      by_cases h1 : i ≤ 4 
      · -- i ≤ 4 
        interval_cases i <;> simp [eq3, eq4, eq5, eq6, eq7] at h_ne ⊢ <;> tauto 
      · -- i > 4 
        have h_gt4 : i > 4 := by omega 
        have h_coeff0 : P.coeff i = 0 := eq8 i h_gt4 
        contradiction 
    · -- Show P.coeff i ≠ 0 if i ∈ {0, 2, 4} 
      rintro (rfl | rfl | rfl)
      · -- i = 0 
        rw [eq3] 
        norm_num 
      · -- i = 2 
        rw [eq5] 
        norm_num 
      · -- i = 4 
        rw [eq7] 
        norm_num
  -- Now rewrite the product over the finite set {0, 2, 4}
  rw [show ∏ᶠ (i : ℕ) (h : P.coeff i ≠ 0), P.coeff i = ∏ᶠ (i ∈ {i | P.coeff i ≠ 0}), P.coeff i by simp]
  rw [h1]
  rw [finprod_mem_eq_toFinset_prod]
  simp [eq3, eq5, eq7]
  <;> norm_num