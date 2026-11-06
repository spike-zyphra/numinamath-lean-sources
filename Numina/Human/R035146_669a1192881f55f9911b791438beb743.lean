import Mathlib

/-How many positive whole numbers have cube roots that are less than $10$? For example, $20$ would count since $\sqrt[3]{20}<10.$-/
theorem algebra_15931 : {n : ℕ | 0 < n ∧ (n : ℝ) ^ ((1 : ℝ) / 3) < 10}.encard = 999 := by
  -- simplify the set to {n : ℕ | 0 < n ∧ n < 1000}
  have AB_eq : {n : ℕ | 0 < n ∧ (n : ℝ) ^ ((1 : ℝ) / 3) < 10} = {n : ℕ | 0 < n ∧ n < 1000} := by
    ext n
    simp
    intro hn
    -- prove n = (n ^ 3⁻¹) ^ 3
    have simp_n : n = ((n : ℝ) ^ (3 : ℝ)⁻¹) ^ 3 := by
        calc
          n = (n : ℝ) := by norm_cast
          _ = (↑n ^ (3 : ℝ)⁻¹) ^ (3 : ℝ) := by rw [@Real.rpow_inv_rpow]; positivity; norm_num
          _ = ((n : ℝ) ^ (3 : ℝ)⁻¹) ^ 3 := by norm_cast 
    -- goal devides into two parts
    apply Iff.intro <;> intro h
    -- when n ^ 3⁻¹ < 10, prove n < 1000
    . -- main expression during the process, "(n ^ 3⁻¹) ^ 3 < 10 ^ 3"
      have ineq : ((n : ℝ) ^ (3 : ℝ)⁻¹) ^ 3 < 10 ^ 3 := by
        apply pow_lt_pow_left --
        simp at h
        exact h
        positivity
        norm_num -- 0 ≠ 3
      simp at ineq

      rw [<-simp_n] at ineq
      norm_cast at ineq ⊢
    -- when n < 1000, prove n ^ 3⁻¹ < 10
    . -- main expression during the process, "(n ^ 3⁻¹) ^ 3 < 10 ^ 3"
      have ineq : ((n : ℝ) ^ (3 : ℝ)⁻¹) ^ 3 < 10 ^ 3 := by
        rw [<-simp_n]
        norm_cast at h ⊢
      
      rw [pow_lt_pow_iff_left] at ineq
      exact ineq
      repeat positivity
  -- prove ncard of {n : ℕ | 0 < n ∧ n < 1000} is 999
  have B_ncard : {n : ℕ | 0 < n ∧ n < 1000}.ncard = 999 := by
    calc
      {n : ℕ | 0 < n ∧ n < 1000}.ncard = (Set.Ioo 0 1000).ncard := by congr
      _ = (Finset.Ioo 0 1000).card := by rw [<-Finset.coe_Ioo, Set.ncard_coe_Finset]
      _ = 999 := by apply Nat.card_Ioo
  
  rw [AB_eq]
  -- prove encard = ncard
  rw [Set.Finite.encard_eq_coe, <-Set.ncard_def, B_ncard] -- Set.ncard = Set.encard.toNat.
  norm_cast
  apply Set.finite_of_ncard_pos -- Show that the set B is finite.
  simp [B_ncard]
