import Mathlib

theorem inequalities_96246 (r : ℝ) (hr : r > 0) :
    ¬(∀ p q : ℝ, p * q ≠ 0 → p * r > q * r → -p > -q) ∧
    ¬(∀ p q : ℝ, p * q ≠ 0 → p * r > q * r → -p > q) ∧
    ¬(∀ p q : ℝ, p * q ≠ 0 → p * r > q * r → 1 > -q / p) ∧
    ¬(∀ p q : ℝ, p * q ≠ 0 → p * r > q * r → 1 < q / p) := by
  constructor
  · -- Prove that (A) is false
    intro h
    have h1 := h 2 1 (by norm_num) (by nlinarith)
    norm_num at h1
  constructor
  · -- Prove that (B) is false
    intro h
    have h2 := h 2 1 (by norm_num) (by nlinarith)
    norm_num at h2
  constructor
  · -- Prove that (C) is false
    intro h
    have h3 := h 1 (-2) (by norm_num) (by nlinarith)
    norm_num at h3
    all_goals linarith
  · -- Prove that (D) is false
    intro h
    have h4 := h 1 (-1) (by norm_num) (by nlinarith)
    norm_num at h4