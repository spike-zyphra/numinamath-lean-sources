import Mathlib

theorem algebra_316495 (p q : ℝ) :
    (∀ x ∈ Set.Icc 1 5, |x^2 + p * x + q| ≤ 2) ↔ (p, q) = (-6, 7) := by
  constructor
  · -- Forward direction: if |x^2 + px + q| ≤ 2 for all x ∈ [1,5], then (p, q) = (-6,7)
    intro h
    have h1 := h 1 (by norm_num)
    have h2 := h 5 (by norm_num)
    have h3 := h 3 (by norm_num)
    have h4 := h 2 (by norm_num)
    have h5 := h 4 (by norm_num)
    have h1'1 : -2 ≤ (1:ℝ)^2 + p * (1:ℝ) + q := by linarith [abs_le.mp h1]
    have h1'2 : (1:ℝ)^2 + p * (1:ℝ) + q ≤ 2 := by linarith [abs_le.mp h1]

    have h2'1 : -2 ≤ (5:ℝ)^2 + p * (5:ℝ) + q := by linarith [abs_le.mp h2]
    have h2'2 : (5:ℝ)^2 + p * (5:ℝ) + q ≤ 2 := by linarith [abs_le.mp h2]

    have h3'1 : -2 ≤ (3:ℝ)^2 + p * (3:ℝ) + q := by linarith [abs_le.mp h3]
    have h3'2 : (3:ℝ)^2 + p * (3:ℝ) + q ≤ 2 := by linarith [abs_le.mp h3]

    have h4'1 : -2 ≤ (2:ℝ)^2 + p * (2:ℝ) + q := by linarith [abs_le.mp h4]
    have h4'2 : (2:ℝ)^2 + p * (2:ℝ) + q ≤ 2 := by linarith [abs_le.mp h4]

    have h5'1 : -2 ≤ (4:ℝ)^2 + p * (4:ℝ) + q := by linarith [abs_le.mp h5]
    have h5'2 : (4:ℝ)^2 + p * (4:ℝ) + q ≤ 2 := by linarith [abs_le.mp h5]
    
    have hp1 : p = -6 := by 
      nlinarith
    have hq1 : q = 7 := by 
      nlinarith
    exact Prod.ext hp1 hq1
  · -- Backward direction: if (p, q) = (-6,7), then |x^2 + px + q| ≤ 2 for all x ∈ [1,5]
    rintro ⟨rfl, rfl⟩
    intro x hx
    have hx1 : 1 ≤ x := by
      have h1 : x ∈ Set.Icc (1 : ℝ) 5 := by
        exact hx
      exact h1.left
    have hx2 : x ≤ 5 := by
      have h1 : x ∈ Set.Icc (1 : ℝ) 5 := by
        exact hx
      exact h1.right
    have h1 : -2 ≤ x^2 + (-6) * x + 7 := by
      nlinarith [sq_nonneg (x - 3)]
    have h2 : x^2 + (-6) * x + 7 ≤ 2 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 5), hx1, hx2]
    apply abs_le.mpr
    constructor <;> nlinarith