import Mathlib

open Real Set
open scoped Real

/-- Given that $\frac{\sin(\alpha + \beta)} {\sin(\alpha - \beta)} = 3$, find the value
of $\frac{\tan \beta} {\tan \alpha}$. -/
theorem Trigonometry_4176 (α β : Real) (hs : sin (α - β) ≠ 0) (hcosα : cos α ≠ 0) (htan : tan β ≠ 0) (h : sin (α + β) / sin (α - β) = 3) : tan α / tan β = 2 := by
  have ⟨hsin, hcos⟩ : sin β ≠ 0 ∧ cos β ≠ 0 := by
    rwa [tan_eq_sin_div_cos, div_ne_zero_iff] at htan
  -- Using the property of trigonometric functions,
  -- we get $\sin \alpha \cos \beta = 2 \cos \alpha \sin \beta$.
  rw [div_eq_iff_mul_eq hs, sin_add, sin_sub, ← sub_eq_zero] at h
  ring_nf at h
  rw [show (4 : ℝ) = 2 * 2 by norm_num, sub_eq_zero, ← mul_assoc, mul_eq_mul_right_iff] at h
  simp at h
  have : sin α * cos β / (cos α * cos β) = (2 * cos α * sin β / (cos α * cos β)) := by
    congr 1
    rw [h]
    ac_rfl
  field_simp [tan_eq_sin_div_cos] at this ⊢
  rw [this, mul_assoc]
