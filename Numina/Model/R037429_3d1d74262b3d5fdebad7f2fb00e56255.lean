import Mathlib

/- If $A$ is an angle such that $\tan A + \sec A = 2,$ enter all possible values of $\cos A,$ separated by commas. -/
-- theorem calculus_16714 (A : ℝ) (hA : Real.tan A + 1 / Real.cos A = 2) :
--     Real.cos A = 4 / 5 := by 

theorem calculus_16714 : {x : ℝ | ∃ A : ℝ, Real.cos A ≠ 0 ∧ Real.tan A + 1 / Real.cos A = 2 ∧ x = Real.cos A} = {4 / 5} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, we show that if `x` is in the left-hand side set, it must equal `4/5`.
    rintro ⟨A, hcos, htan, hx⟩
    have htan_eq : Real.tan A = Real.sin A / Real.cos A := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [htan_eq] at htan
    have h1 : Real.sin A + 1 = 2 * Real.cos A := by 
      field_simp [hcos] at htan ⊢
      linarith
    have h2 : Real.sin A ^ 2 + Real.cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
    have h3 : Real.sin A = 2 * Real.cos A - 1 := by 
      linarith
    rw [h3] at h2
    have h4 : Real.cos A * (5 * Real.cos A - 4) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case $\cos A = 0$ which contradicts $hcos : \cos A ≠ 0$
      exfalso 
      apply hcos 
      all_goals 
      linarith
    · -- Case $5 \cos A - 4 = 0$
      have hcos_eq : Real.cos A = 4 / 5 := by linarith
      linarith [hx, hcos_eq]
  · -- Now the reverse 
    intro h
    rw [h]
    use Real.arccos (4 / 5)
    constructor 
    · -- Show cos A ≠ 0 
      have hcos : Real.cos (Real.arccos (4 / 5)) = 4 / 5 := by 
        apply Real.cos_arccos 
        all_goals norm_num 
      intro h0 
      have h1 : (4 / 5 : ℝ) = 0 := by 
        linarith [hcos, h0] 
      norm_num at h1 
    constructor 
    · -- Show `tan A + 1 / cos A = 2`
      have hcos : Real.cos (Real.arccos (4 / 5)) = 4 / 5 := by 
        apply Real.cos_arccos 
        all_goals norm_num 
      have hsin : Real.sin (Real.arccos (4 / 5)) = 3 / 5 := by 
        have h1 : Real.sin (Real.arccos (4 / 5)) ^ 2 + Real.cos (Real.arccos (4 / 5)) ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq (Real.arccos (4 / 5))
        rw [show Real.cos (Real.arccos (4 / 5)) = 4 / 5 by
            apply Real.cos_arccos 
            all_goals norm_num] at h1 
        have h2 : Real.sin (Real.arccos (4 / 5)) ≥ 0 := by 
          apply Real.sin_nonneg_of_nonneg_of_le_pi 
          · -- Show `0 ≤ Real.arccos (4 / 5)`
            linarith [Real.arccos_nonneg (4 / 5)]
          · -- Show `Real.arccos (4 / 5) ≤ Real.pi`
            linarith [Real.arccos_le_pi (4 / 5)]
        nlinarith 
      have htan_eq : Real.tan (Real.arccos (4 / 5)) = Real.sin (Real.arccos (4 / 5)) / Real.cos (Real.arccos (4 / 5)) := by 
        rw [Real.tan_eq_sin_div_cos]
      rw [htan_eq] 
      rw [hsin, hcos] 
      all_goals norm_num [htan_eq, hcos, hsin]
    all_goals norm_num [Real.cos_arccos]