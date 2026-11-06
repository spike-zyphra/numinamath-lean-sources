import Mathlib

open Real

/- 
Zadatak B-4.1. Ako je


$$

f\left(\log _{3} x\right)=\frac{\log _{3} \frac{9}{x^{4}}}{\log _{0 . \dot{3}} x-\log _{\sqrt{3}} x} \quad \text { i } \quad(f \circ g)(x)=e^{x}

$$


koliko je $g(\ln 2)$ ?
 -/
theorem algebra_201324 {f g : ℝ → ℝ}
    (h₁ : ∀ x > 0, f (logb 3 x) = logb 3 (9 / x^4) / (logb (1/3) x - logb √3 x))
    (h₂ : ∀ x > 0, (f ∘ g) x = exp x)
    (hpos : ∀ x, g x > 0 ∧ 4 - 3 * rexp x ≠ 0) :
    g (log 2) = -1 := by
  have h_third : ∀ x > 0, logb (1 / 3) x = -logb 3 x
  · intro x hx; rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hx,
    one_div, ←rpow_neg_one, ←rpow_mul zero_le_three,
    mul_neg, neg_mul, neg_neg, one_mul,
    rpow_logb three_pos (by norm_num) hx]
  have h_sqrt : ∀ x > 0, logb √3 x = 2 * logb 3 x
  · intro x hx; rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hx, sqrt_eq_rpow,
      ←rpow_mul (by norm_num), ←mul_assoc, one_div_mul_cancel (by norm_num), one_mul,
      rpow_logb (by norm_num) (by norm_num) hx]
  have h_x : ∀ x > 0, logb 3 (9 / x^4) = 2 - 4 * logb 3 x := by intro x hx; rw [logb_div (by norm_num) (by positivity), show (9 : ℝ) = 3^(2 : ℝ) by norm_num, logb_rpow three_pos (by norm_num), logb_pow]; norm_cast
  -- simplify the form of f using these facts
  conv at h₁ => ext x hx; rhs; rw [h_third x hx, h_sqrt x hx, h_x x hx]
  have h_f : ∀ t > 0, f t = (2 - 4 * t) / (-t - 2 * t)
  · intro t ht
    let x := (3 : ℝ)^t
    have ht : logb 3 x = t := logb_rpow (by exact three_pos) (by norm_num)
    have hx : x > 0 := by positivity
    rw [←ht, h₁ x hx]
  -- solve for g x using the equation of the composition
  have hfg : ∀ x > 0, g x * (4 - 3 * rexp x) = 2
  · intro x hx
    have := h₂ x hx
    unfold Function.comp at this
    rw [h_f (g x) (hpos x).left] at this
    rw [←this]
    field_simp [(hpos x).left]
    ring_nf
    rw [pow_two, mul_assoc (g x) (g x) _, mul_inv_cancel₀ (hpos x).left.ne.symm]
    ring
  -- conclude
  have h_g : ∀ x > 0, g x = 2 / (4 - 3 * rexp x)
  · intro x hx
    rw [←hfg x hx]
    rw [mul_div_cancel_right₀ _ (hpos x).right]
  rw [h_g (log 2) (log_pos one_lt_two), exp_log two_pos]
  norm_num