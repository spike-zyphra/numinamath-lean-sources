import Mathlib

theorem algebra_214044 (α β A : ℝ) (h₀ : abs A > 1) (h₁ : Real.sin α = A * Real.sin (α + β)) :
    Real.tan (α + β) = Real.sin β / (Real.cos β - A) := by
  have h2 : Real.sin α = Real.sin (α + β) * Real.cos β - Real.cos (α + β) * Real.sin β := by
    rw [← Real.sin_sub]
    ring
  rw [h2] at h₁
  have h3 : Real.sin (α + β) * Real.cos β - A * Real.sin (α + β) - Real.cos (α + β) * Real.sin β = 0 := by
    linarith
  have h4 : Real.sin (α + β) * (Real.cos β - A) = Real.cos (α + β) * Real.sin β := by
    linarith [h3]
  have h5 : Real.cos (α + β) ≠ 0 := by
    by_contra h
    have h6 : Real.sin (α + β) * (Real.cos β - A) = 0 := by
      rw [h] at h4
      linarith
    have h7 : Real.sin (α + β) ^ 2 + Real.cos (α + β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α + β)
    have h8 : Real.sin (α + β) ^ 2 = 1 := by
      have h9 : Real.sin (α + β) * (Real.cos β - A) = 0 := h6
      have h10 : Real.cos (α + β) = 0 := by
        linarith [h]
      have h11 : Real.sin (α + β) ^ 2 + Real.cos (α + β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α + β)
      rw [h10] at h11
      nlinarith
    have h13 : Real.sin (α + β) ≠ 0 := by
      have h10 : Real.sin (α + β) ^ 2 = 1 := h8
      by_contra h
      rw [h] at h10
      nlinarith
    -- derive cos β = A, which contradicts with |A|>1 because cos^2 β ≤ 1 < A^2
    have h17 : Real.cos β - A = 0 := by
      apply (mul_left_inj' h13).mp
      linarith
    have h18 : Real.cos β = A := by linarith
    have h19 : Real.cos β ^ 2 ≤ 1 := by
      apply Real.cos_sq_le_one
    have h20 : A ^ 2 ≤ 1 := by
      rw [show A = Real.cos β by linarith [h18]]
      nlinarith [h19]
    have h21 : abs A ≤ 1 := by
      have h22 : A ^ 2 ≤ 1 := h20
      have h23 : abs A ≤ 1 := by
        apply abs_le.2
        constructor
        · nlinarith [sq_nonneg (A + 1), sq_nonneg (A - 1), h22]
        · nlinarith [sq_nonneg (A + 1), sq_nonneg (A - 1), h22]
      exact h23
    linarith [h₀, h21]
  -- have proved cos(α+β)≠0
  have h7 : Real.tan (α + β) = Real.sin (α + β) / Real.cos (α + β) := by
    rw [Real.tan_eq_sin_div_cos]
  rw [h7]
  have h9 : Real.cos β - A ≠ 0 := by
    by_contra h
    -- cos β = A
    have h14 : Real.cos β = A := by linarith
    -- cos^2 β + sin^2 β = 1
    -- cos^2 β = A^2 ≤ 1
    -- but |A| > 1
    have h10 : Real.sin (α + β) ^ 2 + Real.cos (α + β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α + β)
    have h13 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
    have h12 : A ^ 2 ≤ 1 := by
      have h14' : Real.cos β = A := by linarith
      have h13' : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
      rw [h14'] at h13'
      nlinarith [h13', Real.sin_sq_le_one β, Real.cos_sq_le_one β]
    have h21 : abs A ≤ 1 := by
      have h22 : A ^ 2 ≤ 1 := h12
      have h23 : abs A ≤ 1 := by
        apply abs_le.2
        constructor
        · nlinarith [sq_nonneg (A + 1), sq_nonneg (A - 1), h22]
        · nlinarith [sq_nonneg (A + 1), sq_nonneg (A - 1), h22]
      exact h23
    linarith [h₀, h21]
  have h4' : Real.sin (α + β) * (Real.cos β - A) = Real.cos (α + β) * Real.sin β := h4
  field_simp [h5, h9] at h4' ⊢
  <;> nlinarith