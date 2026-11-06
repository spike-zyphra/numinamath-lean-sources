import Mathlib

theorem inequalities_53886 (a b c : ℝ) (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x ^ 2 + b * x + c)
  (h₁ : f (-1) ∈ Set.Icc (-1) 1) (h₂ : f 0 ∈ Set.Icc (-1) 1) (h₃ : f 1 ∈ Set.Icc (-1) 1) :
  ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ 3 / 2 := by
  have h1 : -1 ≤ f (-1) := by 
    simpa using h₁.1
  have h2 : f (-1) ≤ 1 := by 
    simpa using h₁.2
  have h3 : -1 ≤ f 0 := by 
    simpa using h₂.1
  have h4 : f 0 ≤ 1 := by 
    simpa using h₂.2
  have h5 : -1 ≤ f 1 := by 
    simpa using h₃.1
  have h6 : f 1 ≤ 1 := by 
    simpa using h₃.2
  have h11 : f (-1) = a - b + c := by
    rw [h₀ (-1)]
    ring
  have h12 : f 0 = c := by 
    rw [h₀ 0]
    ring
  have h13 : f 1 = a + b + c := by 
    rw [h₀ 1]
    ring
  intro x hx
  have hx1 : -1 ≤ x := by 
    have h10 : x ∈ Set.Icc (-1 : ℝ) 1 := hx
    exact h10.1
  have hx2 : x ≤ 1 := by 
    have h10 : x ∈ Set.Icc (-1 : ℝ) 1 := hx
    exact h10.2
  have h14 : f x = a * x ^ 2 + b * x + c := h₀ x 
  rw [h14]
  have h17 : a = (f (-1) + f 1 - 2 * f 0) / 2 := by 
    linarith [h11, h12, h13]
  have h18 : b = (f 1 - f (-1)) / 2 := by 
    linarith [h11, h12, h13]
  have h19 : c = f 0 := by 
    linarith [h12]
  have hx3 : a * x ^ 2 + b * x + c = ((f (-1) + f 1 - 2 * f 0) / 2) * x^2 + ((f 1 - f (-1)) / 2) * x + f 0 := by 
    rw [h17, h18, h19]
    <;> ring_nf 
  have hx4 : -3 / 2 ≤ a * x ^ 2 + b * x + c := by
    rw [hx3]
    nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 0.5), sq_nonneg (x + 0.5),
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ x - (-1) by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
  have hx5 : a * x ^ 2 + b * x + c ≤ 3 / 2 := by 
    rw [hx3]
    nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 0.5), sq_nonneg (x + 0.5),
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ x - (-1) by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
  apply abs_le.mpr
  constructor <;> linarith [hx4, hx5]