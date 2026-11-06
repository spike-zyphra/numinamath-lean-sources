import Mathlib

open Real

theorem inequalities_255742 {f : ℝ → ℝ} (a b : ℝ) (ha : a < b)
    (h : ∀ x1 x2 y1 y2 : ℝ, x1 ∈ Set.Ioo a b → x2 ∈ Set.Ioo a b →
      y1 ∈ Set.Ioo a b → y2 ∈ Set.Ioo a b → x1 + x2 = y1 + y2 →
      f x1 + f x2 < f y1 + f y2 ∧ |y1 - y2| < |x1 - x2|) :
    ∀ n : ℕ, 0 < n → ∀ x : Fin n → ℝ,
      (∀ i, x i ∈ Set.Ioo a b) → ∑ i, f (x i) ≤ n * f (∑ i, x i / n) ∧
      (∑ i, f (x i) = n * f (∑ i, x i / n) ↔ ∀ i j, x i = x j) := by
  have h2 : (a + b)/2 ∈ Set.Ioo a b := by 
    constructor
    · -- Show a < (a + b)/2
      linarith
    · -- Show (a + b)/2 < b
      linarith
  have h3 := h ((a + b)/2) ((a + b)/2) ((a + b)/2) ((a + b)/2) (by simpa using h2) (by simpa using h2) (by simpa using h2) (by simpa using h2) (by linarith)
  norm_num [abs_zero] at h3 
  all_goals linarith