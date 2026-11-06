import Mathlib

/-The inverse of $f(x) = \frac{2x-1}{x+5}$ may be written in the form $f^{-1}(x)=\frac{ax+b}{cx+d}$, where $a$, $b$, $c$, and $d$ are real numbers.  Find $a/c$.-/
theorem algebra_10368 {f : ℝ → ℝ} (hf : f = fun x => (2 * x - 1) / (x + 5)) :
    ∃ a b c d : ℝ, (∀ x ≠ 0, x ≠ 2 → (f ⁻¹' {x}).Nonempty → f ⁻¹' {x} = {(a * x + b) / (c * x + d)}) ∧ a / c = -5 := by
  -- If we substitute $f^{-1}(x)$ into our expression for $f$ we get  \[f(f^{-1}(x))=\frac{2f^{-1}(x)-1}{f^{-1}(x)+5}.\]
  use 5
  use 1
  use -1
  use 2
  constructor
  . intro x hx₁ hx₂ hx₃
    have hx₂: -x + 2 ≠ 0 := by
      rw [@Ne.eq_def]
      rw [@neg_add_eq_zero]
      exact hx₂
    ext y
    simp
    constructor
    . intro hy
      rw [eq_div_iff_mul_eq hx₂]
      rw [hf] at hy
      simp at hy
      have hy₁ : y + 5 ≠ 0 := by
        intro h
        rw [h] at hy
        simp at hy
        absurd hx₁
        exact hy.symm
      have hx₄: -x + 2 = 11/(y + 5) := by
        rw [@neg_add_eq_iff_eq_add, hy.symm, ←add_div]
        rw [show (2 * y - 1 + 11) = 2 * (y + 5) by ring, ←mul_div, div_self hy₁, mul_one]
      rw [hx₄, mul_div, div_eq_iff_mul_eq hy₁, add_mul, mul_assoc, hy.symm, div_mul]
      rw [div_self hy₁, div_one]
      ring_nf
    . intro hy
      rw [hf]
      simp
      have hy₁: y + 5 = 11 / (-x + 2) := by
        rw [show 5 = 5 * (-x + 2) / (-x + 2) by rw [←mul_div, div_self hx₂, mul_one], hy]
        rw [←add_div]
        ring_nf
      have hy₂: y + 5 ≠ 0
      . rw [hy₁]
        simp
        exact hx₂
      rw [div_eq_iff_mul_eq hy₂, hy₁, mul_div, div_eq_iff_mul_eq hx₂]
      rw [sub_mul, mul_assoc, hy, div_mul, div_self hx₂, div_one]
      ring_nf
  . norm_num
