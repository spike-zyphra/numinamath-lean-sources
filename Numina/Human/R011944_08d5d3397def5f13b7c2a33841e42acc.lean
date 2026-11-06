import Mathlib

/-6. Let real numbers $a, b, c, d$ with absolute values greater than 1 satisfy $a b c + a b d + a c d + b c d + a + b + c + d = 0$. Prove: $\frac{1}{a-1} + \frac{1}{b-1} + \frac{1}{c-1} + \frac{1}{d-1} > 0$.-/
theorem algebra_313199 {a b c d : ℝ} (ha : |a| > 1) (hb : |b| > 1) (hc : |c| > 1) (hd : |d| > 1) (h : a * b * c + a * b * d + a * c * d + b * c * d + a + b + c + d = 0) : 1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) + 1 / (d - 1) > 0 := by
  -- $$ \begin{array}{l} \text { 6. Let } x=\frac{a+1}{a-1}, y=\frac{b+1}{b-1}, \ z=\frac{c+1}{c-1}, t=\frac{d+1}{d-1} . \end{array} $$
  let x := (a + 1) / (a - 1)
  let y := (b + 1) / (b - 1)
  let z := (c + 1) / (c - 1)
  let t := (d + 1) / (d - 1)

  -- Given that the absolute values of real numbers $a, b, c, d$ are all greater than 1, we know that $x, y, z, t > 0$, and not equal to 1. 
  have pos_of_abs_gt_1 {x : ℝ} (hx : |x| > 1) : (x + 1) / (x - 1) > 0 := by
    by_cases h : x ≥ 0
    · rw [abs_of_nonneg h] at hx
      apply div_pos
      · linarith only [hx]
      · linarith only [hx]
    · push_neg at h
      rw [abs_of_neg h] at hx
      apply div_pos_of_neg_of_neg
      · linarith only [hx]
      · linarith only [hx]
  have hxpos : x > 0 := by apply pos_of_abs_gt_1 ha
  have hypos : y > 0 := by apply pos_of_abs_gt_1 hb
  have hzpos : z > 0 := by apply pos_of_abs_gt_1 hc
  have htpos : t > 0 := by apply pos_of_abs_gt_1 hd
  have : a - 1 ≠ 0 := by intro h; apply sub_eq_zero.mp at h; simp [h] at ha
  have : b - 1 ≠ 0 := by intro h; apply sub_eq_zero.mp at h; simp [h] at hb
  have : c - 1 ≠ 0 := by intro h; apply sub_eq_zero.mp at h; simp [h] at hc
  have : d - 1 ≠ 0 := by intro h; apply sub_eq_zero.mp at h; simp [h] at hd
  -- From the given condition, we have $x y z t=1$. 
  have hmul : x * y * z * t = 1 := by
    unfold x y z t
    field_simp
    trans (a * b * c * d + a * b + a * c + a * d + b * c + b * d + c * d + 1)
    · apply sub_eq_zero.mp
      rw [←h]
      ring_nf
    · apply sub_eq_zero.mp
      rw [←h]
      ring_nf
  
  -- Thus, the original conclusion becomes $$ \begin{array}{l} \frac{1}{a-1}+\frac{1}{b-1}+\frac{1}{c-1}+\frac{1}{d-1} \ =\frac{x+y+z+t-4}{2} \
  -- > \frac{4 \sqrt[4]{x y z t}-4}{2}=0 . \end{array} $$
  apply lt_of_lt_of_eq (b := (x + y + z + t - 4) / 2)
  · simp
    apply sub_pos.mp
    apply lt_of_lt_of_eq (b := (√x - √y) ^ 2 + (√z - √t) ^ 2 + 2 * (√√(x * y) - √√(z * t)) ^ 2)
    · apply lt_of_le_of_ne
      · positivity
      · by_contra h
        have h₁ : √x = √y := by
          by_contra h₁
          have : (√x - √y) ^ 2 + (√z - √t) ^ 2 + 2 * (√√(x * y) - √√(z * t)) ^ 2 > 0 := by
            apply add_pos_of_pos_of_nonneg ?_ (by positivity)
            apply add_pos_of_pos_of_nonneg ?_ (by positivity)
            apply sq_pos_of_ne_zero
            exact sub_ne_zero_of_ne h₁
          simp [←h] at this
        simp [h₁] at h
        have h₂ : √z = √t := by
          by_contra h₂
          have : (√z - √t) ^ 2 + 2 * (√√(x * y) - √√(z * t)) ^ 2 > 0 := by
            apply add_pos_of_pos_of_nonneg ?_ (by positivity)
            apply sq_pos_of_ne_zero
            exact sub_ne_zero_of_ne h₂
          simp [←h] at this
        simp [h₂] at h
        apply sub_eq_zero.mp at h
        have h₁ : x = y := by
          apply Real.sqrt_inj ?_ ?_ |>.mp h₁
          all_goals positivity
        have h₂ : z = t := by
          apply Real.sqrt_inj ?_ ?_ |>.mp h₂
          all_goals positivity
        rw [h₁, ←h₂, Real.sqrt_mul_self, Real.sqrt_mul_self] at h
        have h₃ : y = z := by
          apply Real.sqrt_inj ?_ ?_ |>.mp h
          all_goals positivity
        rw [h₁, h₃, h₂] at hmul
        have : t ^ 4 = 1 := by rw [←hmul]; ring
        have ht : t = 1 := by
          apply pow_eq_one_iff_of_nonneg ?_ ?_ |>.mp this
          all_goals positivity
        field_simp [t] at ht
        apply sub_eq_zero.mpr at ht
        simp at ht
        all_goals positivity
    · rw [sub_sq, sub_sq, sub_sq, Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt, Real.sq_sqrt]
      rw [mul_assoc, mul_assoc, mul_assoc, ←Real.sqrt_mul,  ←Real.sqrt_mul,  ←Real.sqrt_mul, ←Real.sqrt_mul, ←mul_assoc, hmul]
      simp
      ring
      all_goals positivity
  · unfold x y z t
    field_simp
    ring