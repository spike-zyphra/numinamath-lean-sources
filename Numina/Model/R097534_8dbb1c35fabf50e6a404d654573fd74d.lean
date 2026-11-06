import Mathlib

theorem algebra_249061 (a b : ℕ → ℝ) (d q : ℝ) (h₀ : ∀ n, a n = a 0 + d * n)
    (h₁ : ∀ n, b n = b 0 * q ^ n) (h₂ : a 0 = 1) (h₃ : d ≠ 0) (h₄ : q ≠ 0)
    (h₅ : a 0 + b 0 = 3) (h₆ : a 1 + b 1 = 12) (h₇ : a 2 + b 2 = 23) :
    d + q = 9 := by 
  have hb0 : b 0 = 2 := by
    rw [h₂] at h₅
    linarith
  
  have eq1 : a 1 + b 1 = 12 := h₆
  rw [h₀ 1, h₁ 1] at eq1
  simp [h₂, hb0] at eq1
  
  have eq2 : a 2 + b 2 = 23 := h₇
  rw [h₀ 2, h₁ 2] at eq2
  simp [h₂, hb0] at eq2
  
  have hq : q * (q - 2) = 0 := by
    nlinarith [sq_nonneg (q - 2), sq_nonneg (d), sq_nonneg (q)]
  
  cases' (mul_eq_zero.mp hq) with hq1 hq2
  
  · -- Case q = 0, which is impossible
    exfalso
    exact h₄ (by linarith)
  
  · -- Case q - 2 = 0, so q = 2
    have hq2' : q = 2 := by
      linarith
  
    have eq_d : d = 7 := by
      rw [hq2'] at eq1
      linarith
  
    linarith [eq_d, hq2']