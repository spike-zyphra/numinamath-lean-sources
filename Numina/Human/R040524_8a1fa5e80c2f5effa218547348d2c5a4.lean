import Mathlib

open Real Set

/- Let $x$ and $y$ be nonnegative real numbers such that $x + y = 1.$  Find the maximum value of $$x^4 y + xy^4.$$ -/
theorem algebra_18775
    (valid : (ℝ × ℝ) → Prop)
    (h_valid : ∀ p : (ℝ × ℝ), valid p = (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1))
    (f : (ℝ × ℝ) → ℝ)
    (h_f : ∀ p : (ℝ × ℝ), f p = p.1 ^ 4 * p.2 + p.1 * p.2 ^ 4) :
    IsGreatest (f '' {p | valid p}) (1 / 12) := by
  constructor

  -- 1 / 12 is reachable
  . simp_rw [mem_image, mem_setOf_eq, Prod.exists, h_valid, h_f]
    use ((3 + √ 3) / 6), ((3 - √ 3) / 6)
    constructor
    . exact ⟨
        div_nonneg (add_nonneg zero_le_three (sqrt_nonneg 3)) (Nat.ofNat_nonneg' 6),
        div_nonneg (sub_nonneg.mpr (le_of_lt ((sqrt_lt' three_pos).mpr (show 3 < 3 ^ 2 by norm_num)))) (Nat.ofNat_nonneg' 6),
        by ring_nf ⟩
    . ring_nf
      rw [show √ 3 ^ 4 = (√ 3 ^ 2) ^ 2 by ring, sq_sqrt zero_le_three]
      norm_num

  -- x ^ 4 y + x y ^ 4 ≤ 1 / 12
  . simp only [upperBounds, mem_image, mem_setOf_eq, Prod.exists, forall_exists_index, and_imp]
    intro _ x y h h'
    simp_rw [← h', h_f]
    simp_rw [h_valid] at h
    obtain ⟨_, _, h_xysum⟩ := h

    -- We can write $x ^ 4 y + x y ^ 4 = \frac{3xy (1 - 3xy)}{3}$
    have r1 : x ^ 4 * y + x * y ^ 4 = (3 * x * y * (1 - 3 * x * y)) / 3 := by
      calc
        _ = x * y * (x + y) * (x ^ 2 - x * y + y ^ 2) := by
          ring
        _ = x * y * ((x + y) ^ 2 - 3 * x * y) := by
          conv => lhs; rw [h_xysum]
          ring
        _ = (3 * x * y * (1 - 3 * x * y)) / 3 := by
          rw [h_xysum]
          field_simp
          ring

    -- By AM-GM, $3xy (1 - 3xy) \le \left( \frac{3xy + (1 - 3xy)}{2} \right)^2 = \frac{1}{4},$
    have r2 : 3 * x * y * (1 - 3 * x * y) ≤ 1 / 4 := by
      have AM_GM (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by
        suffices t : 4 * a * b ≤ (a + b) ^ 2 by linarith
        linarith [two_mul_le_add_pow_two a b]
      convert AM_GM (3 * x * y) (1 - 3 * x * y)
      norm_num

    -- so $x^4 y + xy^4 \le \frac{1}{12}.$
    linarith only [r1, r2]
