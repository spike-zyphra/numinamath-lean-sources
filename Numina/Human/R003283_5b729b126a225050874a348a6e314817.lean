import Mathlib

/- Problem 10.5. Show that for any positive real numbers $a, b$ and $c$, the inequality $\sqrt{\frac{a}{b+c}}+\sqrt{\frac{b}{c+a}}+\sqrt{\frac{c}{a+b}}>2$ holds. -/
theorem inequalities_166495 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 < Real.sqrt (a / (b + c)) + Real.sqrt (b / (c + a)) + Real.sqrt (c / (a + b)) := by
  -- We'll use GM-HM inequality
  have hmgm:∀ x y:ℝ, 0<x → 0<y → 2*x*y/(x+y) ≤ √(x*y) ∧ (2*x*y/(x+y) = √(x*y) ↔ x=y)  := by
    intro x y hx hy
    constructor
    · refine (Real.le_sqrt' ?_).mpr ?_
      positivity; rw [div_pow]
      refine (div_le_iff₀' ?_).mpr ?_
      positivity
      suffices 0 ≤ (x + y) ^ 2 * (x * y) - (2*x*y)^2 by linarith
      rw [show (x + y) ^ 2 * (x * y) - (2 * x * y) ^ 2 = (x*y)*(x-y)^2 by ring_nf]
      positivity
    constructor
    · intro h
      apply congr_arg (fun x => x^2) at h; rw [Real.sq_sqrt (by positivity)] at h
      field_simp at h
      apply congr_arg (fun t => t/(x*y)) at h
      rw [show (2 * x * y) ^ 2=4*x*y*(x*y) by ring_nf, show  x * y * (x + y) ^ 2= (x+y)^2*(x*y) by ring_nf, ← mul_div, div_self (by positivity), mul_one, ← mul_div, div_self (by positivity), mul_one] at h
      ring_nf at h
      apply congr_arg (fun t => t-4*x*y) at h
      ring_nf at h; rw [show (-(x * y * 2) + x ^ 2 + y ^ 2) = (x-y)^2 by ring_nf] at h
      nlinarith
    · intro h; rw [h]; ring_nf; rw [Real.sqrt_sq (by positivity), show y^2=y*y by ring_nf, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one];
  -- using on a/(b+c) and 1 with cyclic permutations
  have h01:= hmgm (a/(b+c)) 1 (by positivity) (by norm_num)
  have h02:= hmgm (b/(c+a)) 1 (by positivity) (by norm_num)
  have h03:= hmgm (c/(a+b)) 1 (by positivity) (by norm_num)
  rw [mul_one, mul_div, div_div, mul_add, mul_div, mul_comm (b+c), ← mul_div a, div_self (by positivity), mul_one, mul_one, mul_one, ← add_assoc] at h01
  rw [mul_one, mul_div, div_div, mul_add, mul_div, mul_comm (c+a), ← mul_div b, div_self (by positivity), mul_one, mul_one, mul_one, ← add_assoc] at h02
  rw [mul_one, mul_div, div_div, mul_add, mul_div, mul_comm (a+b), ← mul_div c, div_self (by positivity), mul_one, mul_one, mul_one, ← add_assoc] at h03
  -- we add these three together
  have h1: 2 * a / (a+b+c) + 2 * b / (a+b+c) + 2 * c / (a+b+c) ≤ √(a/(b+c)) + √(b/(c+a)) + √(c/(a+b)) := by gcongr; exact h01.left; rw [show a+b+c=b+c+a by ring_nf]; exact h02.left; rw [show a+b+c=c+a+b by ring_nf]; exact h03.left
  have h1' := h1
  rw [← add_div, ← add_div, ← mul_add, ← mul_add, ← mul_div, div_self (by positivity), mul_one] at h1
  -- let's show that there is no equality by contradiction
  suffices 2 ≠ √(a / (b + c)) + √(b / (c + a)) + √(c / (a + b)) by exact lt_of_le_of_ne h1 this
  by_contra hc'
  -- we can show each of the terms must be equal, therefore a=b+c and cyclic which gives a=b=c=0 -> contradiction
  have h21: 2*a/(a+b+c) = √(a/(b+c)) := by
    by_contra h
    have h':2*a/(a+b+c) < √(a/(b+c)) := by exact lt_of_le_of_ne h01.left h
    have h'':2*a/(a+b+c) + 2*b/(b+c+a) + 2*c/(c+a+b) < √(a/(b+c)) + √(b/(c+a)) + √(c/(a+b)) := by linarith
    rw [show b+c+a=a+b+c by ring, show c+a+b=a+b+c by ring, ← add_div, ← add_div, ← mul_add, ← mul_add, ← mul_div, div_self (by positivity), mul_one] at h''
    linarith
  have h22: 2*b/(b+c+a) = √(b/(c+a)) := by
    by_contra h
    have h':2*b/(b+c+a) < √(b/(c+a)) := by exact lt_of_le_of_ne h02.left h
    have h'':2*a/(a+b+c) + 2*b/(b+c+a) + 2*c/(c+a+b) < √(a/(b+c)) + √(b/(c+a)) + √(c/(a+b)) := by linarith
    rw [show b+c+a=a+b+c by ring, show c+a+b=a+b+c by ring, ← add_div, ← add_div, ← mul_add, ← mul_add, ← mul_div, div_self (by positivity), mul_one] at h''
    linarith
  have h23: 2*c/(c+a+b) = √(c/(a+b)) := by
    by_contra h
    have h':2*c/(c+a+b) < √(c/(a+b)) := by exact lt_of_le_of_ne h03.left h
    have h'':2*a/(a+b+c) + 2*b/(b+c+a) + 2*c/(c+a+b) < √(a/(b+c)) + √(b/(c+a)) + √(c/(a+b)) := by linarith
    rw [show b+c+a=a+b+c by ring, show c+a+b=a+b+c by ring, ← add_div, ← add_div, ← mul_add, ← mul_add, ← mul_div, div_self (by positivity), mul_one] at h''
    linarith
  have h21' := h01.right.mp h21
  have h22' := h02.right.mp h22
  have h23' := h03.right.mp h23
  field_simp at h21' h22' h23'
  linarith