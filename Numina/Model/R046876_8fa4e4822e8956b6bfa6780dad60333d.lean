import Mathlib

theorem algebra_132325 (lambda m : ℝ) (α : ℝ) (a b : ℝ × ℝ)
    (ha : a = (lambda + 2, lambda ^ 2 - Real.cos α ^ 2))
    (hb : b = (m, m / 2 + Real.sin α)) (h : a = 2 * b) :
    lambda / m ∈ Set.Icc (-6) 1 := by
  have eq1 : lambda + 2 = 2 * m := by
    rw [ha, hb] at h
    simp [Prod.ext_iff] at h
    linarith 
  have eq2 : lambda ^ 2 - Real.cos α ^ 2 = 2 * (m / 2 + Real.sin α) := by
    rw [ha, hb] at h
    simp [Prod.ext_iff] at h 
    all_goals 
      linarith
  have hm : m = (lambda + 2) / 2 := by linarith
  have h1 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by
    have hcos : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
    linarith
  rw [h1] at eq2 
  have hmne : m ≠ 0 := by
    by_contra h0
    have hm0 : m = 0 := by linarith
    rw [hm0] at eq1 
    have h00 : lambda + 2 = 0 := by linarith
    have hl0 : lambda = -2 := by linarith
    rw [hm0] at eq2 
    rw [hl0] at eq2 
    nlinarith [Real.sin_sq_le_one α, Real.sin_sq_add_cos_sq α]
  
  constructor
  · -- Show that -6 ≤ lambda / m
    have hmne' : m = (lambda + 2) / 2 := hm
    rw [hmne']
    apply (le_div_iff₀ (by
      nlinarith [sq_nonneg (lambda + 6), sq_nonneg (Real.sin α - 1), sq_nonneg (lambda - 1), Real.sin_sq_le_one α]
    )).mpr 
    nlinarith [sq_nonneg (lambda + 6), sq_nonneg (lambda - 1), Real.sin_sq_le_one α, sq_nonneg (Real.sin α), sq_nonneg (Real.sin α - 1), Real.cos_sq_add_sin_sq α]
  · -- Show that lambda / m ≤ 1
    have hmne' : m = (lambda + 2) / 2 := hm
    rw [hmne']
    apply (div_le_iff₀ (by
      nlinarith [sq_nonneg (lambda + 6), sq_nonneg (Real.sin α - 1), sq_nonneg (lambda - 1), Real.sin_sq_le_one α]
    )).mpr 
    nlinarith [sq_nonneg (lambda - 2), sq_nonneg (lambda + 2), Real.sin_sq_le_one α, sq_nonneg (Real.sin α), sq_nonneg (Real.sin α - 1), Real.cos_sq_add_sin_sq α]