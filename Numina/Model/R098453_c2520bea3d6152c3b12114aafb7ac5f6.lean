import Mathlib

theorem number_theory_327776 (p q : ℕ) (h₀ : 11 * q - 1 ≥ 15 * p) (h₁ : 10 * p ≥ 7 * q + 1)
    (h₂ : 7 / 10 < q / p ∧ q / p < 11 / 15) :
    q = 7 := by
  norm_num at h₂
  <;> omega