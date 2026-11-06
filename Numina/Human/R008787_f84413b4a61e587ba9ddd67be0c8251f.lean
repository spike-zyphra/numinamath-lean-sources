import Mathlib

open Real
open scoped Real

/- 3. Given $\sin \alpha+\cos \alpha=-\frac{3}{\sqrt{5}}$, and $|\sin \alpha|>|\cos \alpha|$, find the value of $\operatorname{tg} \frac{\alpha}{2}$. -/
theorem algebra_274089 (α : ℝ) (h₁ : sin α + cos α = -3 / sqrt 5) (h₂ : abs (sin α) > abs (cos α)) :
    tan (α / 2) = -(sqrt 5 + 1) / 2 := by
  -- first prove (sin α - cos α)^2 = 1/5
  have h₃ : (sin α - cos α)^2 = 1 / 5 := by
    -- square and cancel out (sin α)^2 + (cos α)^2
    ring_nf
    rw [add_assoc, sin_sq_add_cos_sq]
    -- on the other hand square h₁ and also cacnel out (sin α)^2 + (cos α)^2, then rest is just algebraic manipulation
    have := congrArg (fun x ↦ x ^ 2) h₁
    ring_nf at this
    simp at this
    rw [add_assoc, sin_sq_add_cos_sq] at this
    linarith
  -- since 1/5 = (1/√5)^2, we can write the subtraction as positive and negative
  rw [show 1 / 5 = (1 / √5)^2 by simp] at h₃
  replace h₃ : sin α - cos α = 1 / √5 ∨ sin α - cos α = - (1 / √5) := by
    have := pow_eq_pow_iff_of_ne_zero (by norm_num) |>.mp h₃
    simp at this ⊢
    assumption
  have : sin α = - 2 / √5 ∧ cos α = -1 / √5 := by
    -- we'll try both case for subtraction values
    obtain h₃ | h₃ := h₃
      -- for positive, we see that h₂ is not satisifed
    . have : sin α = - 1 / √5 := by linear_combination h₁/2 + h₃/2
      rw [this] at h₂
      have : cos α = - 2 / √5 := by linear_combination h₁/2 - h₃/2
      rw [this] at h₂
      have :  |-1 / √5| < |-2 / √5| := by calc
        |-1 / √5| = 1 / |√5| := by rw [abs_div]; norm_num
        _ < 2 / |√5| := by gcongr; norm_num
        _ = |-2/√5| := by rw [abs_div]; norm_num
      linarith
      -- so must be negative and we get values of sin α and cos α
    . exact ⟨by linear_combination h₁/2 + h₃/2, by linear_combination h₁/2 - h₃/2⟩
  have ⟨hs, hc⟩ := this
  clear * - hs hc
  -- use twice angle formulas to express sin and cos in terms of sin (α/2), cos (α/2)
  have hα : α = 2 * (α / 2) := by ring
  rw [hα] at hs hc
  rw [Real.sin_two_mul] at hs
  rw [Real.cos_two_mul] at hc
  -- prove cos (α/2) ≠ 0 as we'll be using it for division
  have hc' : cos (α/2) ≠ 0 := by
    by_contra h
    rw [h] at hc
    field_simp at hc
  replace hc : 2 * cos (α / 2)^2 = 1 - 1 / √5 := by linear_combination hc
  calc
    -- now express tan ans sin / cos and use the twice angle formulas we proved
    tan (α/2) = (2 * sin (α/2) * cos (α/2)) / (2 * cos (α/2)^2) := by
      rw [tan_eq_sin_div_cos]
      field_simp
      ring
    -- once everything is number, we have to do some denonminator cancellation need (√5 - 1 > 0) for that
    _ = (-2/√5) / (1 - 1/√5) := by rw [hc, hs]
    _ =  -(√ 5 + 1) / 2 := by
      have : √5 - 1 > 0 := by
        suffices √5 > √1 by
          simp at this; linarith
        gcongr; norm_num
      field_simp
      ring_nf
      rw [show √5 ^ 3 = √5 ^2 * √5 by ring]
      simp
      ring