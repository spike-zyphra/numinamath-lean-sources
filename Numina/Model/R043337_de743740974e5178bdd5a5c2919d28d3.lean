import Mathlib

theorem algebra_104764 {a b c d : ℝ} (h₀ : a * b * c - d = 1) (h₁ : b * c * d - a = 2)
    (h₂ : c * d * a - b = 3) (h₃ : d * a * b - c = -6) :
    a + b + c + d ≠ 0 := by 
  have h4 : a * b * c + b * c * d + c * d * a + d * a * b = a + b + c + d := by
    linarith 
  by_contra h
  have h5 : a + b + c + d = 0 := by
    exact_mod_cast h
  -- Now, d = -a -b -c
  have h6 : d = -a - b - c := by 
    linarith 
  -- Substitute d = -a -b -c into h4, which will be LHS =0 and RHS =0.
  have h7 : a * b * c + b * c * d + c * d * a + d * a * b = 0 := by
    have eq1 : d = -a - b - c := h6
    rw [eq1] at h4
    linarith 
  have h8 : (a + b) * (b + c) * (c + a) = 0 := by 
    have eq1 : d = -a - b - c := h6
    have eq2 : a * b * c + b * c * d + c * d * a + d * a * b = 0 := h7
    rw [eq1] at eq2 
    linarith [sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a), sq_nonneg (a + b + c), sq_nonneg (a * b * c)]
  
  cases' (mul_eq_zero.mp h8) with h9 h10
  · cases' (mul_eq_zero.mp h9) with h11 h12
    · -- Case where a + b = 0
      have eq4 : b = -a := by linarith 
      have eq5 : d = -c := by 
        have h7 : d = -a - b - c := h6 
        rw [show b = -a by linarith [eq4]] at h7
        linarith 
      have h8 : a * b * c - d = 1 := by linarith [h₀]
      have h9 : b * c * d - a = 2 := by linarith [h₁]
      have h10 : c * d * a - b = 3 := by linarith [h₂]
      have h11 : d * a * b - c = -6 := by linarith [h₃]
      rw [show b = -a by linarith [eq4], show d = -c by linarith [eq5]] at h8 h9 h10 h11
      nlinarith [sq_nonneg (a), sq_nonneg (c), sq_nonneg (a * c), sq_nonneg (a + c), sq_nonneg (a - c)]
    · -- Case where b + c = 0
      have eq4 : c = -b := by linarith 
      have eq5 : d = -a := by 
        have h8 : d = -a - b - c := h6 
        rw [show c = -b by linarith [eq4]] at h8 
        linarith 
      have h8 : a * b * c - d = 1 := by linarith [h₀]
      have h9 : b * c * d - a = 2 := by linarith [h₁]
      have h10 : c * d * a - b = 3 := by linarith [h₂]
      have h11 : d * a * b - c = -6 := by linarith [h₃]
      rw [show c = -b by linarith [eq4], show d = -a by linarith [eq5]] at h8 h9 h10 h11
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a * b), sq_nonneg (a + b), sq_nonneg (a - b)]
  · -- Case where c + a = 0
    have eq4 : c = -a := by linarith 
    have eq5 : d = -b := by 
      have h8 : d = -a - b - c := h6 
      rw [show c = -a by linarith [eq4]] at h8 
      linarith 
    have h8 : a * b * c - d = 1 := by linarith [h₀]
    have h9 : b * c * d - a = 2 := by linarith [h₁]
    have h10 : c * d * a - b = 3 := by linarith [h₂]
    have h11 : d * a * b - c = -6 := by linarith [h₃]
    rw [show c = -a by linarith [eq4], show d = -b by linarith [eq5]] at h8 h9 h10 h11
    nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a * b), sq_nonneg (a + b), sq_nonneg (a - b)]