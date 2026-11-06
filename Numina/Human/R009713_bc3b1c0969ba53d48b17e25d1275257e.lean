import Mathlib

open Complex

/-Let $x,$ $y,$ $z$ be real numbers, all greater than 3, so that
\[\frac{(x + 2)^2}{y + z - 2} + \frac{(y + 4)^2}{z + x - 4} + \frac{(z + 6)^2}{x + y - 6} = 36.\]Enter the ordered triple $(x,y,z).$-/
theorem algebra_14593 (a b c : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
  (h : a ^ 2 / (b * c) + b ^ 2 / (a * c) + c ^ 2 / (a * b) = -1) :
  ‖a + b + c‖ = 1 ∨ ‖a + b + c‖ = 2 := by
    -- Since $|a| = 1,$ $a \overline{a} = |a|^2,$ so $\overline{a} = \frac{1}{a}.$
    -- Similarly, $\overline{b} = \frac{1}{b}$ and $\overline{c} = \frac{1}{c}.$
    have ha' := Complex.inv_eq_conj ha
    have hb' := Complex.inv_eq_conj hb
    have hc' := Complex.inv_eq_conj hc
    have ane0 : a ≠ 0 := fun a0 => by simp [a0] at ha
    have bne0 : b ≠ 0 := fun b0 => by simp [b0] at hb
    have cne0 : c ≠ 0 := fun c0 => by simp [c0] at hc
    -- Also, let $z = a + b + c.$
    set z := a + b + c with hz
    -- Then
    -- \begin{align*}
    -- |z|^2 &= |a + b + c|^2 \\
    -- &= (a + b + c)(\overline{a + b + c}) \\
    -- &= (a + b + c)(\overline{a} + \overline{b} + \overline{c}) \\
    -- &= (a + b + c) \left( \frac{1}{a} + \frac{1}{b} + \frac{1}{c} \right) \\
    -- &= (a + b + c) \cdot \frac{ab + ac + bc}{abc}.
    -- \end{align*}
    have hz' : ‖z‖^2 = (a + b + c) * (a*b + a*c + b*c) / (a*b*c) := by
      rw [←Complex.conj_mul', hz]
      simp [←ha', ←hb', ←hc']
      field_simp
      ring_nf
    -- We have that
    -- \[z^3 = (a + b + c)^3 = (a^3 + b^3 + c^3) + 3(a^2 b + ab^2 + a^2 c + ac^2 + b^2 c + bc^2) + 6abc,\]so
    -- \begin{align*}
    -- 3|z|^2 &= \frac{3(a^2 b + ab^2 + a^2 c + ac^2 + b^2 c + bc^2) + 3abc}{abc} \\
    -- &= \frac{z^3 - (a^3 + b^3 + c^3) + 3abc}{abc}.
    -- \end{align*}
    have c1 : 3 * ‖z‖^2 = (z^3 - (a^3 + b^3 + c^3) + 3*a*b*c) / (a*b*c) := by
      rw [hz']
      field_simp
      ring_nf
    have c2 : a^3 + b^3 + c^3 = -a*b*c := by
      field_simp at h
      have : (a^3 + b^3 + c^3) * (a*b*c) = -(b * c * (a * c) * (a * b)) := by
        rw [←h]
        ring_nf
      rw [show -(b * c * (a * c) * (a * b)) = -(a*b*c) * (a*b*c) by ring] at this
      rw [mul_eq_mul_right_iff] at this
      simp [ane0, bne0, cne0] at this
      convert this using 1; ring
    simp only [ c2, neg_mul, sub_neg_eq_add] at c1
    -- From the equation $\frac{a^2}{bc} + \frac{b^2}{ac} + \frac{c^2}{ab} = -1,$ $a^3 + b^3 + c^3 = -abc,$ so
    -- \[3|z|^2 = \frac{z^3 + 4abc}{abc} = \frac{z^3}{abc} + 4.\]Then
    -- \[3|z|^2 - 4 = \frac{z^3}{abc},\]so
    -- \[\left| 3|z|^2 - 4 \right| = \left| \frac{z^3}{abc} \right| = |z|^3.\]
    have c3 :  3 * ‖z‖^2 - 4 = z^3 / (a*b*c) := by
      rw [c1]
      field_simp
      ring
    have : ‖(3 * ‖z‖ ^ 2 - 4)‖ = ‖z ^ 3 / (a * b * c)‖ := by rw [←c3]; norm_cast
    simp [ha, hb, hc] at this
    by_cases hneg : 3 * Complex.abs z ^ 2 - 4 < 0
    · -- Let $r = |z|,$ so $|3r^2 - 4| = r^3.$  If $3r^2 - 4 < 0,$ then
      -- \[4 - 3r^2 = r^3.\]This becomes $r^3 + 3r^2 - 4 = 0,$ which factors as $(r - 1)(r + 2)^2 = 0.$  Since $r$ must be nonnegative, $r = 1.$
      simp [ abs_of_neg hneg] at this
      have : (abs z - 1) * (abs z + 2)^2 = 0 := by nlinarith
      rw [mul_eq_zero] at this
      rcases this with h | h <;> simp
      · have : abs z = 1 := by linarith
        tauto
      · have : 0 ≤ abs z := AbsoluteValue.nonneg Complex.abs z
        nlinarith
    · -- If $3r^2 - 4 \ge 0,$ then
      -- \[3r^2 - 4 = r^3.\]This becomes $r^3 - 3r^2 + 4 = 0,$ which factors as $(r + 1)(r - 2)^2 = 0.$  Since $r$ must be nonnegtaive, $r = 2.$
      push_neg at hneg
      simp [_root_.abs_of_nonneg hneg] at this
      have : (abs z + 1) * (abs z - 2)^2 = 0 := by nlinarith
      rw [mul_eq_zero] at this
      rcases this with h | h <;> simp
      · have : 0 ≤ abs z := AbsoluteValue.nonneg Complex.abs z
        nlinarith
      · have : abs z = 2 := by nlinarith
        tauto
