import Mathlib

/- Let $a, b$ and $c$ be positive real numbers. Prove that

$$
\frac{8}{(a+b)^{2}+4 a b c}+\frac{8}{(b+c)^{2}+4 a b c}+\frac{8}{(c+a)^{2}+4 a b c}+a^{2}+b^{2}+c^{2} \geq \frac{8}{a+3}+\frac{8}{b+3}+\frac{8}{c+3}
$$ -/
theorem inequalities_605430 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    8 / ((a + b) ^ 2 + 4 * a * b * c) +
    8 / ((b + c) ^ 2 + 4 * a * b * c) +
    8 / ((c + a) ^ 2 + 4 * a * b * c) +
    a ^ 2 + b ^ 2 + c ^ 2 ≥
    8 / (a + 3) + 8 / (b + 3) + 8 / (c + 3) := by
  -- Show that (x + y)² + 4xyz ≤ 2(x² + y²)(z + 1) for all x, y, z > 0.
  have lemma₁ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) ^ 2 + 4 * x * y * z ≤ 2 * (x ^ 2 + y ^ 2) * (z + 1) := by
    nlinarith [sq_nonneg (x - y)]
  -- Show that 8 / (2 * (x ^ 2 + y ^ 2) * (z + 1)) ≥ 4 / √(2 * (z + 1)) for all x, y, z > 0.
  have lemma₂ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 8 / (2 * (x ^ 2 + y ^ 2) * (z + 1)) + (x ^ 2 + y ^ 2) / 2 ≥ 4 / Real.sqrt (2 * (z + 1)) := by
    -- Use AM-GM to prove the inequality.
    rw [ge_iff_le]
    apply le_of_sq_le_sq
    rw [div_pow, Real.sq_sqrt, show (4 ^ 2 : ℝ) = 2 * 8 by norm_num, mul_div_mul_left, show (8 : ℝ) = 2 * 4 by norm_num, mul_assoc, mul_div_mul_left]
    have := sq_nonneg (4 / ((x ^ 2 + y ^ 2) * (z + 1)) - (x ^ 2 + y ^ 2) / 2)
    -- Expand the square in the goal and hypothesis at the same time.
    rw [sub_sq] at this
    rw [add_sq]
    rw [<-mul_div_assoc, mul_assoc, mul_comm _ (x ^ 2 + y ^ 2)] at this ⊢
    nth_rewrite 2 [div_mul_eq_div_div] at this ⊢
    rw [<-mul_div_assoc, <-mul_div_assoc, <-mul_div_assoc, mul_comm (x ^ 2 + y ^ 2) 4, mul_div_cancel_right₀] at this ⊢
    linarith only [this]
    apply ne_of_gt (by positivity)
    apply ne_of_gt (by positivity)
    norm_num
    norm_num
    positivity
    positivity
  have lemma₃ (x : ℝ) (hx : 0 < x) : x + 3 ≥ 2 * Real.sqrt (2 * (x + 1)) := by
    -- Show that x + 3 ≥ √(2(x + 1)) by squaring both sides.
    rw [ge_iff_le]
    apply le_of_sq_le_sq
    rw [mul_pow, Real.sq_sqrt]
    linarith only [sq_nonneg (x - 1)]
    positivity
    positivity
  calc
    8 / ((a + b) ^ 2 + 4 * a * b * c) + 8 / ((b + c) ^ 2 + 4 * a * b * c) + 8 / ((c + a) ^ 2 + 4 * a * b * c) + a ^ 2 + b ^ 2 + c ^ 2
    _ = 8 / ((a + b) ^ 2 + 4 * a * b * c) + 8 / ((b + c) ^ 2 + 4 * b * c * a) + 8 / ((c + a) ^ 2 + 4 * c * a * b) + a ^ 2 + b ^ 2 + c ^ 2 := by
      -- Simply change the order of terms in multiplying a, b and c.
      ac_rfl
    _ ≥ 8 / (2 * (a ^ 2 + b ^ 2) * (c + 1)) + 8 / (2 * (b ^ 2 + c ^ 2) * (a + 1)) + 8 / (2 * (c ^ 2 + a ^ 2) * (b + 1)) + a ^ 2 + b ^ 2 + c ^ 2 := by
      -- Use lemma₁ to show that $ \frac{8}{(a+b)^{2}+4 a b c} \geq \frac{4}{\left(a^{2}+b^{2}\right)(c+1)} $, and similar for the other two terms.
      rw [ge_iff_le]
      apply add_le_add
      apply add_le_add
      apply add_le_add
      apply add_le_add
      apply add_le_add
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity) (lemma₁ a b c ha hb hc)
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity) (lemma₁ b c a hb hc ha)
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity) (lemma₁ c a b hc ha hb)
      all_goals
        rfl
    _ = 8 / (2 * (a ^ 2 + b ^ 2) * (c + 1)) + 8 / (2 * (b ^ 2 + c ^ 2) * (a + 1)) + 8 / (2 * (c ^ 2 + a ^ 2) * (b + 1)) + (a ^ 2 + b ^ 2) / 2 + (b ^ 2 + c ^ 2) / 2 + (c ^ 2 + a ^ 2) / 2 := by
      rw [add_assoc, add_assoc]
      symm
      rw [add_assoc, add_assoc]
      congrm ?_ + ?_
      . rfl
      . ring_nf
    _ = (8 / (2 * (a ^ 2 + b ^ 2) * (c + 1)) + (a ^ 2 + b ^ 2) / 2) + (8 / (2 * (b ^ 2 + c ^ 2) * (a + 1)) + (b ^ 2 + c ^ 2) / 2) + (8 / (2 * (c ^ 2 + a ^ 2) * (b + 1)) + (c ^ 2 + a ^ 2) / 2) := by
      -- Group terms together to have $ \frac{4}{\left(a^{2}+b^{2}\right)(c+1)}+\frac{a^{2}+b^{2}}{2} \geq 2 \sqrt{\frac{2}{c+1}}$ and respective terms for b, c.
      ring_nf
    _ ≥ 4 / Real.sqrt (2 * (c + 1)) + 4 / Real.sqrt (2 * (a + 1)) + 4 / Real.sqrt (2 * (b + 1)) := by
      -- Use lemma₂ to show that $ \frac{4}{\left(a^{2}+b^{2}\right)(c+1)}+\frac{a^{2}+b^{2}}{2} \geq 2 \sqrt{\frac{2}{c+1}}$ and respective terms for b, c.
      apply add_le_add
      apply add_le_add
      apply lemma₂ a b c ha hb hc
      apply lemma₂ b c a hb hc ha
      apply lemma₂ c a b hc ha hb
    _ ≥ 8 / (c + 3) + 8 / (a + 3) + 8 / (b + 3) := by
      -- Show that 4 / √(2(c + 1)) ≤ 8 / (c + 3), and respective terms for a and b.
      apply add_le_add
      apply add_le_add
      rw [show (4 : ℝ) = 8 / 2 by norm_num, div_div]
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity) (lemma₃ c hc)
      rw [show (4 : ℝ) = 8 / 2 by norm_num, div_div]
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity) (lemma₃ a ha)
      rw [show (4 : ℝ) = 8 / 2 by norm_num, div_div]
      apply div_le_div₀ (by norm_num) (by rfl) (by positivity) (lemma₃ b hb)
    _ = 8 / (a + 3) + 8 / (b + 3) + 8 / (c + 3) := by
      -- Show that the inequality holds by simply rearrange terms.
      ac_rfl

