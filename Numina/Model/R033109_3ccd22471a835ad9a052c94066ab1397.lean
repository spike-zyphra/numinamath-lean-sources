import Mathlib

open Real Set
open scoped Real

theorem algebra_232813 {f : ℝ → ℝ}
  (hf : f = λ x => sqrt (sin x ^ 4 + 4 * cos x ^ 2) - sqrt (cos x ^ 4 + 4 * sin x ^ 2)) :
  IsGreatest (range f) 1 ∧ IsLeast (range f) (-1) := by
  have eq1 : ∀ x, f x = Real.sqrt (sin x ^ 4 + 4 * cos x ^ 2) - Real.sqrt (cos x ^ 4 + 4 * sin x ^ 2) := by
    intro x
    rw [hf]
  
  have h1 : 1 ∈ range f := by
    use (0 : ℝ)
    rw [eq1]
    have h2 : sin (0 : ℝ) = 0 := by simp
    have h3 : cos (0 : ℝ) = 1 := by simp
    rw [h2, h3]
    have h4 : Real.sqrt ((0 : ℝ) ^ 4 + 4 * (1 : ℝ) ^ 2) = 2 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
      all_goals norm_num
    have h5 : Real.sqrt ((1 : ℝ) ^ 4 + 4 * (0 : ℝ) ^ 2) = 1 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
      all_goals norm_num
    rw [h4, h5]
    all_goals norm_num
  -- Need to show that 1 is the greatest
  have h1' : ∀ y ∈ range f, y ≤ 1 := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [eq1] at hx
    -- Simplify the function
    have h2 : Real.sqrt (sin x ^ 4 + 4 * cos x ^ 2) = (cos x) ^ 2 + 1 := by
      have h3 : sin x ^ 4 + 4 * cos x ^ 2 = ((cos x) ^ 2 + 1) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - 1), sq_nonneg ((cos x) ^ 2 - 1)]
      rw [h3]
      have h4 : ((cos x) ^ 2 + 1 : ℝ) ≥ 0 := by
        nlinarith [sq_nonneg (cos x ^ 2), Real.sin_sq_add_cos_sq x]
      rw [Real.sqrt_sq (h4)]
      <;> nlinarith
      all_goals nlinarith 
    have h3 : Real.sqrt (cos x ^ 4 + 4 * sin x ^ 2) = 2 - (cos x) ^ 2 := by
      have h4 : cos x ^ 4 + 4 * sin x ^ 2 = ((cos x) ^ 2 - 2) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - 1), sq_nonneg ((cos x) ^ 2 - 1)]
      rw [h4]
      have h5 : ((cos x) ^ 2 - 2 : ℝ) ≤ 0 := by
        nlinarith [sq_nonneg (cos x ^ 2 - 1)]
      have h6 : Real.sqrt (((cos x) ^ 2 - 2 : ℝ) ^ 2) = - ((cos x) ^ 2 - 2) := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonpos (by linarith)]
        all_goals linarith
      rw [h6]
      all_goals ring_nf <;> linarith
    rw [h2, h3] at hx
    -- Show bounded above by 1
    have h4 : (cos x) ^ 2 ≤ 1 := by
      have h5 : (cos x) ^ 2 ≤ 1 := by
        have h6 : -1 ≤ cos x ∧ cos x ≤ 1 := by
          constructor
          · linarith [Real.neg_one_le_cos x]
          · linarith [Real.cos_le_one x]
        nlinarith
        all_goals nlinarith
      linarith
    all_goals nlinarith [sq_nonneg (cos x ^ 2 - 1), sq_nonneg ((sin x) ^ 2 - 1), Real.sin_sq_add_cos_sq x]
 
  have h2 : -1 ∈ range f := by
    use Real.pi / 2
    rw [eq1]
    have h2 : sin (Real.pi / 2 : ℝ) = 1 := by
      exact sin_pi_div_two
    have h3 : cos (Real.pi / 2 : ℝ) = 0 := by
      exact cos_pi_div_two
    rw [h2, h3]
    have h4 : Real.sqrt ((1 : ℝ) ^ 4 + 4 * (0 : ℝ) ^ 2) = 1 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
      all_goals norm_num
    have h5 : Real.sqrt ((0 : ℝ) ^ 4 + 4 * (1 : ℝ) ^ 2) = 2 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
      all_goals norm_num
    rw [h4, h5]
    all_goals norm_num

  -- Show that -1 is the least
  have h2' : ∀ y ∈ range f, -1 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [eq1] at hx
    -- Simplify the function
    have h2 : Real.sqrt (sin x ^ 4 + 4 * cos x ^ 2) = (cos x) ^ 2 + 1 := by
      have h3 : sin x ^ 4 + 4 * cos x ^ 2 = ((cos x) ^ 2 + 1) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - 1), sq_nonneg ((cos x) ^ 2 - 1)]
      rw [h3]
      have h4 : ((cos x) ^ 2 + 1 : ℝ) ≥ 0 := by
        nlinarith [sq_nonneg (cos x ^ 2), Real.sin_sq_add_cos_sq x]
      rw [Real.sqrt_sq (h4)]
      <;> nlinarith
      all_goals nlinarith 
    have h3 : Real.sqrt (cos x ^ 4 + 4 * sin x ^ 2) = 2 - (cos x) ^ 2 := by
      have h4 : cos x ^ 4 + 4 * sin x ^ 2 = ((cos x) ^ 2 - 2) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - 1), sq_nonneg ((cos x) ^ 2 - 1)]
      rw [h4]
      have h5 : ((cos x) ^ 2 - 2 : ℝ) ≤ 0 := by
        nlinarith [sq_nonneg (cos x ^ 2 - 1)]
      have h6 : Real.sqrt (((cos x) ^ 2 - 2 : ℝ) ^ 2) = - ((cos x) ^ 2 - 2) := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonpos (by linarith)]
        all_goals linarith
      rw [h6]
      all_goals ring_nf <;> linarith
    rw [h2, h3] at hx
    -- Show bounded above by 1
    have h4 : (cos x) ^ 2 ≤ 1 := by
      have h5 : (cos x) ^ 2 ≤ 1 := by
        have h6 : -1 ≤ cos x ∧ cos x ≤ 1 := by
          constructor
          · linarith [Real.neg_one_le_cos x]
          · linarith [Real.cos_le_one x]
        nlinarith
        all_goals nlinarith
      linarith
    nlinarith [sq_nonneg (cos x ^ 2 - 0), sq_nonneg ((sin x) ^ 2 - 1), Real.sin_sq_add_cos_sq x]

  constructor 
  · -- Show that 1 is greatest in the range of f
    exact ⟨h1, h1'⟩
  · -- Show that -1 is least in the range of f
    exact ⟨h2, h2'⟩
  all_goals try tauto