import Mathlib

/-
The function $f$ defined by $f(x) = \frac{ax + b}{cx + d}$, where $a$, $b$, $c$, and $d$ are nonzero real numbers, has the properties $f(19) = 19$, $f(97) = 97$, and $f(f(x)) = x$ for all values except $-\frac{d}{c}$. Find the unique number that is not in the range of $f$.
-/
theorem algebra_96747 {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
(hd : d ≠ 0) (f : ℝ → ℝ) (hf : ∀ x , (c * x + d ≠ 0) →  f x = (a * x + b) / (c * x + d))
(h19 : (c * 19 + d ≠ 0) ∧ f 19 = 19) (h97 : (c * 97 + d ≠ 0) ∧ f 97 = 97) (hff : ∀ x, (c * x + d ≠ 0) → (c * (f x) + d ≠ 0) ∧ f (f x) = x) :
a / c = 58 := by
--We first need to show that $d=-a$, using the condition $f(f(x))=x$.
  have had : d = -a := by
--We observe f(0)=b/d and thus f(b/d)=0.
    have hf0 := hf 0 (by simp [hd])
    simp only [mul_zero, zero_add] at hf0
    specialize hff 0 (by simp [hd])
    rw [hf0] at hff
    have := hf (b/d)
    specialize this hff.1
--We substitute f(b/d) in the formula for f.
    rw [hff.2, eq_div_iff_mul_eq hff.1, zero_mul, mul_div, mul_comm, ← mul_div] at this
    nth_rw 2 [(by simp only [mul_one] : b = b * 1)] at this
    rw [← mul_add, zero_eq_mul] at this
--Simplifying, we obtain $b=0$ or $a/d+1=0$. Clearly, the second is true, and it implies $d=-a$.
    cases this
    · contradiction
    · rw [← add_eq_zero_iff_eq_neg]
      have : d+a = 0 ↔ (d+a)/d =0 :=by simp only [div_eq_zero_iff, hd, or_false]
      rw [this, add_div, div_self hd, add_comm]
      assumption
--From the condition on $f(97)$, we deduce $2*97*a+b=97^2*c$.
  have eq1 : 2 * 97 * a + b = 97^2 * c := by
    specialize hf 97 h97.1
    rw [h97.2, had, eq_div_iff_mul_eq] at hf
    ring_nf at hf
    linarith
    rw [← had]
    exact h97.1
--From the condition on $f(19)$, we deduce $2*19*a+b=19^2*c$.
  have eq2 : 2 * 19 * a + b = 19^2 * c := by
    specialize hf 19 h19.1
    rw [h19.2, had, eq_div_iff_mul_eq] at hf
    ring_nf at hf
    linarith
    rw [← had]
    exact h19.1
--Combining the two equations, we obtain $a/c=58$.
  have eqdiff : 2 * 78 * a = (97^2-19^2) * c := by linarith
  rw [mul_comm, ← div_eq_div_iff hc (by norm_num)] at eqdiff
  norm_num at eqdiff
  exact eqdiff