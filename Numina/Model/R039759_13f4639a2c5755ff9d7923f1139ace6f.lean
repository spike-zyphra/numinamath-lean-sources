import Mathlib

theorem inequalities_1547 (r b w : ℕ)
    (h₀ : b ≥ (w / 2 : ℝ)) (h₁ : b ≤ (r / 3 : ℝ)) (h₂ : w + b ≥ 55) :
    r ≥ 57 := by
  have h3 : (b : ℝ) ≥ (w / 2 : ℝ) := by linarith
  have h4 : (w : ℝ) ≤ (2 * (b : ℝ) : ℝ) := by
    nlinarith
  have h5 : w ≤ 2 * b := by
    have h6 : (w : ℝ) ≤ (2 * (b : ℝ) : ℝ) := h4
    have h7 : (w : ℝ) ≤ (2 * b : ℝ) := by
      nlinarith
    have h8 : (w : ℝ) ≤ (2 * b : ℝ) := h7
    have h9 : (w : ℕ) ≤ (2 * b : ℕ) := by
      exact_mod_cast (show (w : ℝ) ≤ (2 * b : ℝ) from h8)
    linarith
  have h7 : 3 * b ≥ 55 := by
    omega
  have h8 : b ≥ 19 := by
    omega
  have h9 : (b : ℝ) ≤ (r / 3 : ℝ) := by linarith
  have h10 : (3 * (b : ℝ) : ℝ) ≤ (r : ℝ) := by
    nlinarith
  have h11 : 3 * b ≤ r := by
    have h12 : (3 * (b : ℝ) : ℝ) ≤ (r : ℝ) := h10
    have h13 : (3 * b : ℝ) ≤ (r : ℝ) := by
      linarith
    have h14 : (3 * b : ℕ) ≤ (r : ℕ) := by
      exact_mod_cast (show (3 * b : ℝ) ≤ (r : ℝ) from h13)
    linarith
  have h12 : 3 * b ≥ 57 := by
    omega
  omega