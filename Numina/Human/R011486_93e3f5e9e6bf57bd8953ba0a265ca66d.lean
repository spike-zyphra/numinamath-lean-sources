import Mathlib

/-
A special case of Newton's inequality
By Newton's inequality, we have $$\left(\frac{\sum a b c}{4}\right)^{2} \geqslant \frac{\sum a b}{6} a b c d$$
-/
lemma newton_inequality_1 (a b c d : ℝ) :
    (a * b * c + b * c * d + c * d * a + d * a * b) ^ 2 / 16 ≥ (a * b + b * c + c * d + d * a + a * c + b * d) / 6 * a * b * c * d := by
  field_simp
  apply div_le_div_iff₀ (by positivity) (by positivity) |>.mpr
  apply sub_nonneg.mp
  ring_nf
  trans 2 * (a * b * c - b * c * d) ^ 2 + 2 * (b * c * d - c * d * a) ^ 2 + 2 * (c * d * a - d * a * b) ^ 2 + 2 * (d * a * b - a * b * c) ^ 2 + 2 * (a * b * c - c * d * a) ^ 2 + 2 * (b * c * d - d * a * b) ^ 2
  · positivity
  · apply le_of_eq
    ring

/- A special case of Newton's inequality
By Newton's inequality, we have $$\left(\frac{\sum a b c}{4}\right)^{2} \geqslant \frac{\sum a b}{6} a b c d$$
-/
lemma newton_inequality_2 (a b c d : ℝ) :
    ((a * b + b * c + c * d + d * a + a * c + b * d) / 6) ^ 2 ≥ (a + b + c + d) / 4 * ((a * b * c + b * c * d + c * d * a + d * a * b) / 4) := by
  field_simp
  apply div_le_div_iff₀ (by positivity) (by positivity) |>.mpr
  apply sub_nonneg.mp
  ring_nf
  trans 2 * (a * b - b * c) ^ 2 + 2 * (b * c - c * d) ^ 2 + 2 * (c * d - d * a) ^ 2 + 2 * (d * a - a * b) ^ 2 +
    2 * (a * b - a * c) ^ 2 + 2 * (b * c - b * d) ^ 2 + 2 * (c * d - c * a) ^ 2 + 2 * (d * a - d * b) ^ 2 +
    2 * (a * c - b * c) ^ 2 + 2 * (b * d - c * d) ^ 2 + 2 * (c * a - d * a) ^ 2 + 2 * (d * b - a * b) ^ 2 +
    8 * (a * b - c * d) ^ 2 + 8 * (b * c - d * a) ^ 2 + 8 * (a * c - b * d) ^ 2
  · positivity
  · apply le_of_eq
    ring

/-
Example 11.8 (Crux) $a, b, c, d \geqslant 0$, prove that
$$(a+b)^{3}(b+c)^{3}(c+d)^{3}(d+a)^{3} \geqslant 16 a^{2} b^{2} c^{2} d^{2}(a+b+c+d)^{4}$$
-/
theorem inequalities_600262
    (a b c d : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    (a + b) ^ 3 * (b + c) ^ 3 * (c + d) ^ 3 * (d + a) ^ 3 ≥
    16 * a ^ 2 * b ^ 2 * c ^ 2 * d ^ 2 * (a + b + c + d) ^ 4 := by
  -- Assume $a+b+c+d=1$,
  wlog h : a + b + c + d = 1 with H
  · by_cases h' : a + b + c + d = 0
    · have ha : a = 0 := by
        apply le_antisymm ?_ ha
        by_contra h
        push_neg at h
        have : a + b + c + d > 0 := by linarith only [h, hb, hc, hd]
        linarith only [this, h']
      simp [ha] at h'
      have hb : b = 0 := by
        apply le_antisymm ?_ hb
        by_contra h
        push_neg at h
        have : b + c + d > 0 := by linarith only [h, hb, hc, hd]
        linarith only [this, h']
      simp [hb] at h'
      have hc : c = 0 := by
        apply le_antisymm ?_ hc
        by_contra h
        push_neg at h
        have : c + d > 0 := by linarith only [h, hc, hd]
        linarith only [this, h']
      simp [hc] at h'
      simp [ha, hb, hc, hd]
    · let t := a + b + c + d
      have ht : t > 0 := by
        apply lt_of_le_of_ne
        · positivity
        · apply Ne.symm
          exact h'
      let a' := a / t
      let b' := b / t
      let c' := c / t
      let d' := d / t
      have h : a' + b' + c' + d' = 1 := by
        unfold a' b' c' d'
        field_simp
      obtain H := H a' b' c' d' (by positivity) (by positivity) (by positivity) (by positivity) h
      unfold a' b' c' d' at H
      apply mul_le_mul_of_nonneg_left (a := t ^ 12) at H
      obtain H := H (by positivity)
      field_simp at H
      rw [show t ^ 2 * t ^ 2 * t ^ 2 * t ^ 2 = t ^ 8 by rw [←pow_add, ←pow_add, ←pow_add]] at H
      rw [show t ^ 3 * t ^ 3 * t ^ 3 * t ^ 3 = t ^ 12 by rw [←pow_add, ←pow_add, ←pow_add]] at H
      field_simp at H
      apply le_trans ?_ H
      apply le_of_eq
      rw [mul_comm (t ^ 12), mul_div_assoc]
      congr
      field_simp
      rw [←pow_add]
  · -- note that $(a+b)(b+c)(c+d)(d+a)$ is cyclic symmetric rather than fully symmetric, we attempt to bring it closer to a symmetric polynomial. $$\begin{array}{l} (a+b)(b+c)(c+d)(d+a)= \ a^{2} c^{2}+b^{2} d^{2}+2 a b c d+\sum a b c(a+b+c)= \ (a c-b d)^{2}+\sum a b c(a+b+c+d) \geqslant \ a b c+b c d+c d a+d a b \end{array}$$
    rw [h, one_pow, mul_one]
    have : (a + b) * (b + c) * (c + d) * (d + a) ≥ a * b * c + b * c * d + c * d * a + d * a * b := by
      trans (a * c - b * d) ^ 2 + (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)
      · apply le_of_eq
        ring
      · simp [h]
        positivity
    -- apply newton_inequality, obtain that \frac{\sum a b}{6} a b c d \geqslant \sqrt{\frac{\sum a}{4} \frac{\sum a b c}{4} a b c d}
    have : ((a * b * c + b * c * d + c * d * a + d * a * b) ^ 2 / 16) ^ 2 ≥ (a + b + c + d) / 4 * ((a * b * c + b * c * d + c * d * a + d * a * b) / 4) * (a * b * c * d) ^ 2 := by
      trans ((a * b + b * c + c * d + d * a + a * c + b * d) / 6 * a * b * c * d) ^ 2
      · gcongr
        apply newton_inequality_1
      trans ((a * b + b * c + c * d + d * a + a * c + b * d) / 6) ^ 2 * (a * b * c * d) ^ 2
      · apply le_of_eq
        ring
      · gcongr
        apply newton_inequality_2
    have : ((a * b * c + b * c * d + c * d * a + d * a * b) ^ 2) ^ 2 ≥ 16 * (a * b * c + b * c * d + c * d * a + d * a * b) * (a * b * c * d) ^ 2 := by
      field_simp at this
      apply le_div_iff₀ (by simp) |>.mp at this
      apply le_trans ?_ this
      field_simp [h]
      apply le_of_eq
      ring
    -- Thus, $$(a b c+b c d+c d a+d a b)^{3} \geqslant 16 a^{2} b^{2} c^{2} d^{2}(a+b+c+d)$$
    have : (a * b * c + b * c * d + c * d * a + d * a * b) ^ 3 ≥ 16 * (a * b * c * d) ^ 2 := by
      by_cases h : a * b * c + b * c * d + c * d * a + d * a * b = 0
      · simp [h]
        by_contra h'
        simp at h'
        have : a * b * c * d > 0 := by
          apply lt_of_le_of_ne
          · positivity
          · apply Ne.symm
            exact sq_pos_iff.mp h'
        have ha : a > 0 := by
          apply lt_of_le_of_ne ha
          by_contra h
          simp [←h] at this
        have hb : b > 0 := by
          apply lt_of_le_of_ne hb
          by_contra h
          simp [←h] at this
        have hc : c > 0 := by
          apply lt_of_le_of_ne hc
          by_contra h
          simp [←h] at this
        have hd : d > 0 := by
          apply lt_of_le_of_ne hd
          by_contra h
          simp [←h] at this
        have : a * b * c + b * c * d + c * d * a + d * a * b > 0 := by positivity
        linarith only [this, h]
      · push_neg at h
        apply le_of_mul_le_mul_of_pos_left (a := a * b * c + b * c * d + c * d * a + d * a * b)
        · apply le_of_eq_of_le ?_ (le_of_le_of_eq this ?_)
          · ring
          · ring
        · apply lt_of_le_of_ne
          · positivity
          · exact id (Ne.symm h)
    -- Hence, the proposition is proved! Before this, we have introduced examples of converting the denominator to the same symmetric expression, and we can also approach the same monomial denominator.
    simp [mul_pow, ←mul_assoc] at this
    apply le_trans this
    rw [←mul_pow, ←mul_pow, ←mul_pow]
    gcongr
