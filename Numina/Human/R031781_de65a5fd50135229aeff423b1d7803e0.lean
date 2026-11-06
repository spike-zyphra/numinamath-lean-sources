import Mathlib

open Real

theorem algebra_279704 {f : ℝ → ℝ} (hf : ∀ x, -1 < x ∧ x < 1 → f x = log ((1 + x) / (1 - x))) (x : ℝ) :
  -1 < x ∧ x < 1 →
    f ((3 * x + x ^ 3) / (1 + 3 * x ^ 2)) = 3 * f x := by
  -- let x_range : Set ℝ := { x | -1 < x ∧ x < 1 }
  intro hx
  generalize h_a: (3 * x + x^3) / (1 + 3 * x^2) = a
  have h₀: (1 + x)^3 = 1 + x * 3 + x^2 * 3 + x^3 := by ring_nf
  have h₁: (1 - x)^3 = 1 - x * 3 + x^2 * 3 - x^3 := by ring_nf
  have h₂: 1 + a = (1 + x)^3 / (1 + 3 * x^2) := by
    rw [<-h_a]
    field_simp
    ring
  have h₃: 1 - a = (1 - x)^3 / (1 + 3 * x^2) := by
    rw [<-h_a]
    field_simp
    ring
  have h₄: 0 < 1 + 3 * x^2 := by
    apply lt_add_of_pos_of_le (by simp)
    bound
  have h₅: -1 < a ∧ a < 1 := by
    rw [<-h_a]
    constructor
    · simp [lt_div_iff₀ h₄, neg_lt_iff_pos_add]
      ring_nf
      rw [<-h₀]
      bound
    · simp [div_lt_iff₀ h₄, <-sub_pos]
      ring_nf
      rw [add_sub, <-h₁]
      bound
  rw [hf a h₅]
  field_simp [h₂, h₃]
  rw [hf x hx]
  rw [<-Real.log_rpow (by bound) 3, Real.div_rpow (by apply le_of_lt; bound) (by bound) ]
  norm_cast
