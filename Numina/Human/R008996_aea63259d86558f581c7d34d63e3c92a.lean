import Mathlib

open Real Set

/- 288*. Prove that if $\alpha$ and $\beta$ are acute angles and $\alpha<\beta$, then $\frac{\operatorname{tg} \alpha}{\alpha} > \frac{\operatorname{tg} \beta}{\beta}$. -/
theorem inequalities_130371 (α β : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : α < β) : tan α / α < tan β / β := by
  -- define f(x) = tan(x) / x
  set f := fun x => tan x / x
  -- it is enough to show that f is strictly monotone on (0, π / 2)
  suffices StrictMonoOn f (Ioo 0 (π / 2)) from this h₀ h₁ h₂
  dsimp [f]
  -- show that f is differentiable and its derivative is positive
  -- on (0, π / 2)
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  -- f is continuous on (0, π / 2)
  · apply ContinuousOn.div
    · apply ContinuousOn.mono continuousOn_tan_Ioo
      intro x hx
      simp only [mem_Ioo] at hx ⊢
      constructor <;> linarith
    · exact continuousOn_id' (Ioo 0 (π / 2))
    · simp only [mem_Ioo, ne_eq, and_imp]
      intro x hx1 hx2
      linarith
  -- it is left to show that f'(x) > 0 for all x ∈ (0, π / 2)
  simp only [interior_Ioo, mem_Ioo, and_imp]
  intro x hx1 hx2
  have hcos0 {x} (hx1 : 0 < x) (hx2 : x < π / 2) : cos x ≠ 0 := by
    apply ne_of_gt
    apply cos_pos_of_mem_Ioo
    rw [mem_Ioo]
    constructor <;> linarith
  have dtan : DifferentiableAt ℝ tan x := by
    rw [differentiableAt_tan]
    exact hcos0 hx1 hx2
  rw [deriv_div dtan differentiableAt_id' (by linarith)]
  rw [deriv_id'', deriv_tan, tan_eq_sin_div_cos, mul_one]
  field_simp
  -- simplify the expression of f'(x) and get sin(x) / cos(x) < x / cos(x) ^ 2
  -- to prove this inequality, show that sin(x) < x and 0 < cos(x) ≤ cos(x) ^ 2
  apply div_lt_div₀ (sin_lt hx1) _ (le_of_lt hx1)
  · apply sq_pos_of_ne_zero (hcos0 hx1 hx2)
  · suffices 0 ≤ cos x * (1 - cos x) by
      apply le_of_sub_nonneg
      ring_nf at this
      exact this
    apply mul_nonneg
    · apply cos_nonneg_of_mem_Icc
      rw [mem_Icc]
      constructor <;> linarith
    · linarith [cos_le_one x]