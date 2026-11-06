import Mathlib

theorem algebra_299690 (A : ℝ → ℝ) (hA : A = fun x => (2 - x) - Real.sqrt 2 * (Real.sqrt 2 * x - 5)) :
    {x : ℕ | 0 < A x}.Finite ∧ {x : ℕ | 0 < A x}.ncard > 2 := by

  have h1 : ∀ x : ℕ, A x = (2 - (x : ℝ)) - Real.sqrt 2 * (Real.sqrt 2 * (x : ℝ) - 5) := by 
    intro x
    rw [hA]

  have h2 : {x : ℕ | 0 < A x} = {0, 1, 2, 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, h1]
    constructor
    · -- Assume h > 0, prove x in {0, 1, 2, 3}
      intro h
      have h3 : (2 - (x : ℝ)) - Real.sqrt 2 * (Real.sqrt 2 * (x : ℝ) - 5) > 0 := by 
        simpa using h
      have h4 : (x : ℝ) < (2 + 5 * Real.sqrt 2) / 3 := by 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      have h5 : x < 4 := by 
        by_contra h
        push_neg at h
        have h6 : x ≥ 4 := by omega
        have h7 : (x : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h6 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      interval_cases x <;> norm_num at h3 ⊢ <;> tauto
    · -- Assume x in {0,1,2,3}, prove h > 0
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 0 
        norm_num [h1]
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      · -- x = 1 
        norm_num [h1]
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      · -- x = 2 
        norm_num [h1]
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      · -- x = 3 
        norm_num [h1]
        <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), mul_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  rw [h2] 
  constructor
  · -- Show {0, 1, 2, 3} is finite 
    have h3 : ( ({0, 1, 2, 3} : Set ℕ) : Set ℕ).Finite := by 
      have h5 : ( ({0, 1, 2, 3} : Set ℕ) : Set ℕ) = (Finset.Icc (0 : ℕ) 3).toSet := by 
        ext x 
        simp 
        <;> omega 
      rw [h5]
      apply Set.toFinite 
    exact h3
  · -- Show {0, 1, 2, 3}.ncard > 2
    have h7 : (({0, 1, 2, 3} : Set ℕ) : Set ℕ).ncard = 4 := by
      have h8 : ( ({0, 1, 2, 3} : Set ℕ) : Set ℕ ) = (Finset.Icc (0 : ℕ) 3).toSet := by 
        ext x 
        simp 
        <;> omega 
      rw [h8] 
      rw [Set.ncard_coe_Finset] 
      simp 
      <;> try { native_decide } 
    have h4 : (({0, 1, 2, 3} : Set ℕ) : Set ℕ).ncard > (2 : ℕ) := by
      omega
    exact h4