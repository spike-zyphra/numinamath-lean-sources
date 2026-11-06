import Mathlib

theorem algebra_13958 {f : ℤ → ℤ} (a b : ℤ) (h₀ : f = fun x => a * x + b)
    (h₁ : f (f 0) = 0) (h₂ : f (f (f 4)) = 9) :
    ∑ i ∈ Finset.range 2015, f (f (f (f i))) = 2029105 := by
  have h3 : a * b + b = 0 := by
    simp [h₀] at h₁
    linarith 
  have h4 : b * (a + 1) = 0 := by
    linarith [h3] 
  cases' (mul_eq_zero.mp h4) with hb h5
  · -- Case where b = 0
    have hb0 : b = 0 := hb 
    simp [h₀, hb0] at h₂
    have h6 : 4 * a ^ 3 = 9 := by
      nlinarith 
    exfalso
    have h7 : a ≤ 1 := by 
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + 1), sq_nonneg (a - 1)]
    have h8 : a ≥ 1 := by
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + 1), sq_nonneg (a - 1)]
    have h10 : a ≥ 0 := by
      nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + 1), sq_nonneg (a - 1)]
    interval_cases a <;> omega 
  · -- Case where a + 1 = 0
    have ha : a = -1 := by 
      linarith 
    have hb13 : b = 13 := by 
      simp [h₀, ha] at h₂ 
      nlinarith 
    simp [h₀, ha, hb13] 
    <;> native_decide