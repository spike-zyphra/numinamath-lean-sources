import Mathlib

/- Let $x,$ $y,$ and $z$ be positive real numbers such that $x + y + z = 1.$  Find the maximum value of $x^3 y^2 z.$ -/
theorem algebra_12871 :
    IsGreatest {w : ℝ | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = 1 ∧ w = x ^ 3 * y ^ 2 * z} (1 / 432) := by
  -- We need to prove the AM-GM inequality for the case n = 2, then n = 4, then n = 3, then n = 6.
  have am_gm_2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b ≤ ((a + b) / 2) ^ 2 := by
    linarith only [show 0 ≤ (a - b) ^ 2 by positivity]
  have am_gm_4 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : a * b * c * d ≤ ((a + b + c + d) / 4) ^ 4 := by
    calc
      a * b * c * d = (a * b) * (c * d) := by ac_rfl
      _ ≤ ((a + b) / 2) ^ 2 * ((c + d) / 2) ^ 2 := by apply mul_le_mul; apply am_gm_2 a b; exact ha; exact hb; apply am_gm_2 c d; positivity; positivity; positivity; positivity
      _ = ((a + b) * (c + d)) ^ 2 / 16 := by field_simp; ring_nf
      _ ≤ ((((a + b) + (c + d)) / 2) ^ 2) ^ 2 / 16 := by apply div_le_div_of_nonneg_right; rw [pow_le_pow_iff_left]; apply am_gm_2 (a + b) (c + d); positivity; positivity; positivity; positivity; norm_num; norm_num
      _ = ((a + b + c + d) / 2) ^ 4 / 16 := by rw [<-pow_mul]; norm_num; ac_rfl
      _ = ((a + b + c + d) / 4) ^ 4 := by rw [div_pow, div_pow, div_div]; norm_num
  have am_gm_3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a * b * c ≤ ((a + b + c) / 3) ^ 3 := by
    by_cases h : 0 < (a + b + c) / 3
    . specialize am_gm_4 a b c ((a + b + c) / 3)
      simp [ha, hb, hc, show 0 ≤ (a + b + c) / 3 by positivity] at am_gm_4
      rw [show (a + b + c) + (a + b + c) / 3 = (a + b + c) / 3 * 4 by ring_nf] at am_gm_4
      simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        IsUnit.mul_div_cancel_right] at am_gm_4
      rw [show 4 = 3 + 1 by norm_num, pow_add, pow_one] at am_gm_4
      rw [mul_le_mul_right] at am_gm_4
      exact am_gm_4
      exact h
    . simp at h
      replace h : a + b + c = 0 := by
        linarith only [ha, hb, hc, h]
      have ha : a = 0 := by
        linarith only [ha, hb, hc, h]
      have hb : b = 0 := by
        linarith only [ha, hb, hc, h]
      have hc : c = 0 := by
        linarith only [ha, hb, hc, h]
      rw [ha, hb, hc]
      norm_num
  have am_gm_6 (a b c d e f : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) : a * b * c * d * e * f ≤ ((a + b + c + d + e + f) / 6) ^ 6 := by
    have lm (x : ℝ) (y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x / 3) ^ 3 * (y / 3) ^ 3 ≤ ((x + y) ^ 2) ^ 3 / 46656 := by
      calc
        (x / 3) ^ 3 * (y / 3) ^ 3 = (4 * x * y) ^ 3 / 46656 := by field_simp; ring_nf
        _ ≤ ((x + y) ^ 2) ^ 3 / 46656 := by apply div_le_div_of_nonneg_right; rw [pow_le_pow_iff_left₀]; linarith only [show 0 ≤ (x - y) ^ 2 by positivity]; positivity; positivity; norm_num; norm_num
    calc
      a * b * c * d * e * f = (a * b * c) * (d * e * f) := by ac_rfl
      _ ≤ ((a + b + c) / 3) ^ 3 * ((d + e + f) / 3) ^ 3 := by apply mul_le_mul; apply am_gm_3 a b c ha hb hc; apply am_gm_3 d e f hd he hf; positivity; positivity
      _ ≤ (((a + b + c) + (d + e + f)) ^ 2) ^ 3 / 46656 := by apply lm (a + b + c) (d + e + f); positivity; positivity
      _ = ((a + b + c + d + e + f) ^ 2) ^ 3 / 46656 := by ac_rfl
      _ = ((a + b + c + d + e + f) / 6) ^ 6 := by rw [<-pow_mul]; rw [div_pow]; norm_num
  simp [IsGreatest, upperBounds, -one_div]
  refine ⟨?_, ?_⟩
  . -- When x = 1 / 2, y = 1 / 3, z = 1 / 6, the maximum value is obtained.
    use 1 / 2
    simp
    use 1 / 3
    simp
    use 1 / 6
    norm_num
  . -- Show that 1 / 432 is the upper bound of any possible value.
    intro w x xpos y ypos z zpos hsum hw
    suffices h : (x / 3) * (x / 3) * (x / 3) * (y / 2) * (y / 2) * z ≤ 1 / 432 / 108 by
      rw [show (x / 3) * (x / 3) * (x / 3) * (y / 2) * (y / 2) * z = w / 108 by rw [hw]; field_simp; ring_nf] at h
      rw [div_le_div_iff_of_pos_right] at h
      exact h
      norm_num
    calc
      x / 3 * (x / 3) * (x / 3) * (y / 2) * (y / 2) * z ≤ (((x / 3) + (x / 3) + (x / 3) + (y / 2) + (y / 2) + z) / 6) ^ 6 := by apply am_gm_6 (x / 3) (x / 3) (x / 3) (y / 2) (y / 2) z; positivity; positivity; positivity; positivity; positivity; positivity
      _ = ((x + y + z) / 6) ^ 6 := by rw [show (x / 3) + (x / 3) + (x / 3) + (y / 2) + (y / 2) + z = x + y + z by ring_nf]
      _ = 1 / 432 / 108 := by rw [hsum]; norm_num
