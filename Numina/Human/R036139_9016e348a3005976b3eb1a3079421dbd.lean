import Mathlib

open Real Set
open scoped Real

/- Suppose that $\sec x+\tan x=\frac{22}7.$  Find $\csc x+\cot x.$ -/
theorem calculus_22112 (x : ℝ) (hcos_ne_zero : cos x ≠ 0) (_ : sin x ≠ 0)
    (h : 1 / cos x + tan x = 22 / 7) :
    1 / sin x + cot x = 29 / 15 := by
  --We can write the given equation as
  --\[\frac{1}{\cos x} + \frac{\sin x}{\cos x} = \frac{1 + \sin x}{\cos x} = \frac{22}{7},\]
  --so $\cos x = \frac{7}{22} (1 + \sin x).$
  field_simp [tan_eq_sin_div_cos] at h
  apply_fun (· / 22) at h
  rw [mul_div_cancel_left₀ _ (by norm_num), eq_comm] at h
  --Substituting into $\cos^2 x + \sin^2 x = 1,$ we get
  --\[\frac{49}{484} (1 + \sin x)^2 + \sin^2 x = 1.\]
  have csq_add_ssq := cos_sq_add_sin_sq x
  -- This simplifies to $533 \sin^2 x + 98 \sin x - 435 = 0,$
  rw [h, ← sub_eq_zero] at csq_add_ssq
  apply_fun (484 * ·) at csq_add_ssq
  ring_nf at csq_add_ssq
  -- which factors as $(\sin x + 1)(533 \sin x - 435) = 0,$
  replace csq_add_ssq : (sin x + 1) * (533 * sin x - 435) = 0 := by linear_combination csq_add_ssq
  -- so $\sin x = -1$ or $\sin x = \frac{435}{533}.$
  rw [mul_eq_zero] at csq_add_ssq
  rcases csq_add_ssq with hsin | hsin
  -- If $\sin x = -1,$ then $\cos x = 0,$ which makes $\sec x + \tan x$ undefined.
  . rw [add_comm, hsin] at h
    norm_num [h] at hcos_ne_zero
  -- Therefore, $\sin x = \frac{435}{533},$ and
  apply_fun (533⁻¹ * ·) at hsin
  replace hsin : sin x = 533⁻¹ * 435 := by linear_combination hsin
  -- $\cos x = \frac{7}{22} (1 + \sin x) = \frac{308}{533}.$
  rw [hsin] at h
  --Then
  --\[\csc x + \cot x = \frac{1}{\sin x} + \frac{\cos x}{\sin x}  = \frac{1 + \cos x}{\sin x} = \frac{1 + \frac{308}{533}}{\frac{435}{533}} = \boxed{\frac{29}{15}}.\]
  rw [cot_eq_cos_div_sin, h, hsin]
  norm_num
