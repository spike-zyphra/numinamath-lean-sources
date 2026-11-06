import Mathlib

/- Let $x, y, z$ be real numbers greater than -1 . Prove that

$$
\frac{1+x^{2}}{1+y+z^{2}}+\frac{1+y^{2}}{1+z+x^{2}}+\frac{1+z^{2}}{1+x+y^{2}} \geq 2
$$ -/
theorem algebra_606066 (x y z : ℝ) (hx : -1 < x) (hy : -1 < y) (hz : -1 < z) : (1 + x ^ 2) / (1 + y + z ^ 2) + (1 + y ^ 2) / (1 + z + x ^ 2) + (1 + z ^ 2) / (1 + x + y ^ 2) ≥ 2 := by
  -- Set a = 1 + x², b = 1 + y², c = 1 + z².
  let a := 1 + x ^ 2
  let b := 1 + y ^ 2
  let c := 1 + z ^ 2
  -- It suffices to show that a / (2c + b) + b / (2a + c) + c / (2b + a) ≥ 1.
  suffices a / (2 * c + b) + b / (2 * a + c) + c / (2 * b + a) ≥ 1 by
    -- Substitute a = 1 + x², b = 1 + y², c = 1 + z² back into the goal.
    simp only [a, b, c] at this
    -- We have $y \leq \frac{1+y^{2}}{2}$, hence $\frac{1+x^{2}}{1+y+z^{2}} \geq \frac{1+x^{2}}{1+z^{2}+\frac{1+y^{2}}{2}}$ and the similar inequalities.
    calc
      (1 + x ^ 2) / (1 + y + z ^ 2) + (1 + y ^ 2) / (1 + z + x ^ 2) + (1 + z ^ 2) / (1 + x + y ^ 2)
      _ ≥ 2 * ((1 + x ^ 2) / (2 * (1 + z ^ 2) + (1 + y ^ 2)) + (1 + y ^ 2) / (2 * (1 + x ^ 2) + (1 + z ^ 2)) + (1 + z ^ 2) / (2 * (1 + y ^ 2) + (1 + x ^ 2))) := by
        rw [mul_add, mul_add, mul_div, mul_div, mul_div]
        nth_rewrite 2 [<-@mul_div_cancel₀ _ _ 2 (1 + y ^ 2) (by norm_num)]
        nth_rewrite 3 [<-@mul_div_cancel₀ _ _ 2 (1 + z ^ 2) (by norm_num)]
        nth_rewrite 4 [<-@mul_div_cancel₀ _ _ 2 (1 + x ^ 2) (by norm_num)]
        rw [<-mul_add, <-mul_add, <-mul_add, mul_div_mul_left _ _ (by norm_num), mul_div_mul_left _ _ (by norm_num), mul_div_mul_left _ _ (by norm_num)]
        rw [ge_iff_le]
        apply add_le_add
        apply add_le_add
        . -- Use the fact that $y \leq \frac{1+y^{2}}{2}$.
          apply div_le_div_of_nonneg_left
          positivity
          linarith only [hy, show 0 ≤ z ^ 2 by positivity]
          rw [add_assoc, add_comm y (z ^ 2), add_assoc]
          apply add_le_add (by rfl)
          apply add_le_add (by rfl)
          linarith only [show 0 ≤ (y - 1) ^ 2 by positivity]
        . -- Use the fact that $z \leq \frac{1+z^{2}}{2}$.
          apply div_le_div_of_nonneg_left
          positivity
          linarith only [hz, show 0 ≤ x ^ 2 by positivity]
          rw [add_assoc, add_comm z (x ^ 2), add_assoc]
          apply add_le_add (by rfl)
          apply add_le_add (by rfl)
          linarith only [show 0 ≤ (z - 1) ^ 2 by positivity]
        . -- Use the fact that $x \leq \frac{1+x^{2}}{2}$.
          apply div_le_div_of_nonneg_left
          positivity
          linarith only [hx, show 0 ≤ y ^ 2 by positivity]
          rw [add_assoc, add_comm x (y ^ 2), add_assoc]
          apply add_le_add (by rfl)
          apply add_le_add (by rfl)
          linarith only [show 0 ≤ (x - 1) ^ 2 by positivity]
      _ ≥ 2 := by
        -- Simply use the hypothesis that a / (2c + b) + b / (2a + c) + c / (2b + a) ≥ 1.
        rw [show 1 + x ^ 2 = a by simp [a], show 1 + y ^ 2 = b by simp [b], show 1 + z ^ 2 = c by simp [c]] at this ⊢
        linarith only [this]
  -- Prove the Titu's lemma (an alternate form of Cauchy-Schwarz inequality).
  have titu_lemma_3var (u1 u2 u3 : ℝ) (v1 v2 v3 : ℝ) (hv1 : 0 < v1) (hv2 : 0 < v2) (hv3 : 0 < v3) :
      (u1 ^ 2 / v1 + u2 ^ 2 / v2 + u3 ^ 2 / v3) ≥ (u1 + u2 + u3) ^ 2 / (v1 + v2 + v3) := by
    -- Make sure the sum of denominators is positive. 
    have h₁ : 0 < v1 + v2 + v3 := by linarith
    -- Clear the denominator by multiplying both sides by v1 + v2 + v3, then simplify.
    field_simp [h₁.ne']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- Apply Cauchy-Schwarz inequality by expanding.
    nlinarith [sq_nonneg (u1 * v2 - u2 * v1), sq_nonneg (u2 * v3 - u3 * v2), sq_nonneg (u3 * v1 - u1 * v3), sq_nonneg (u1 * v3 - u3 * v1), sq_nonneg (u2 * v1 - u1 * v2), sq_nonneg (u3 * v2 - u2 * v3), mul_pos hv1 hv2, mul_pos hv2 hv3, mul_pos hv3 hv1]
  -- Show that a / (2c + b) + b / (2a + c) + c / (2b + a) ≥ 1.
  calc
    a / (2 * c + b) + b / (2 * a + c) + c / (2 * b + a)
    _ = a ^ 2 / (a * (2 * c + b)) + b ^ 2 / (b * (2 * a + c)) + c ^ 2 / (c * (2 * b + a)) := by
      -- Multiply both numerators and denominators of each term by a, b, c respectively.
      rw [pow_two, pow_two, pow_two, mul_div_mul_left, mul_div_mul_left, mul_div_mul_left]
      . simp [c]
        positivity
      . simp [b]
        positivity
      . simp [a]
        positivity
    _ ≥ (a + b + c) ^ 2 / (a * (2 * c + b) + b * (2 * a + c) + c * (2 * b + a)) := by
      -- Apply Titu's lemma.
      apply titu_lemma_3var
      repeat positivity
    _ ≥ 1 := by
      -- Use the fact that (a - b)² + (b - c)² + (c - a)² ≥ 0 (equivalently, (a + b + c)² ≥ 3(ab + bc + ca)) to show the desired inequality.
      rw [ge_iff_le, le_div_iff₀ (by positivity)]
      linarith only [show 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 by positivity]


