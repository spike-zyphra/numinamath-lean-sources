import Mathlib

open Real

theorem algebra_231378 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 1 → x ≠ -1 → f x = (x + 1) / (x - 1)) :
    ∀ x, x ≠ 1 → x ≠ -1 → f x * f (-x) = 1 := by
  intro x hx1 hx2
  have hfx : f x = (x + 1) / (x - 1) := hf x hx1 hx2
  have hf_neg_x1 : -x ≠ 1 := by
    intro h_eq
    have h_eqm1 : x = -1 := by
      linarith
    tauto
  have hf_neg_x2 : -x ≠ -1 := by
    intro h_eq_neg
    -- h_eq_neg: -x = -1
    have h_eq1 : x = 1 := by
      linarith
    tauto
  have hf_neg_x : f (-x) = (-x + 1) / (-x - 1) := hf (-x) hf_neg_x1 hf_neg_x2
  rw [hfx, hf_neg_x]
  have h1 : x - 1 ≠ 0 := by
    intro h_eq
    apply hx1
    linarith
  have h2 : -x - 1 ≠ 0 := by
    intro h_eq
    have h_eqm1 : x = -1 := by
      linarith
    tauto
  field_simp [(show (x - 1 : ℝ) ≠ 0 by assumption), (show (-x - 1 : ℝ) ≠ 0 by assumption)]
  <;> ring