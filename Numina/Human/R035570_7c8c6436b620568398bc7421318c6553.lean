import Mathlib

/-
Find the maximum value of
\[\frac{x - y}{x^4 + y^4 + 6}\]over all real numbers $x$ and $y.$
-/
theorem algebra_21748 :
    IsGreatest {z : ℝ | ∃ x y, z = (x - y) / (x ^ 4 + y ^ 4 + 6)} (1 / 4) := by
  unfold IsGreatest
  constructor
  -- the max value is at x=1, y=-1
  . simp
    use 1
    use -1
    ring_nf
  . unfold upperBounds
    simp
    intro z x y hz
    rw [hz]
    -- subsitute y with -y, to remove negative sign.
    let y' := -y
    have y_eq_neg_y' : y = -y' := by ring
    rw [y_eq_neg_y']
    simp
    rw [neg_pow y' 4]
    norm_num
    let y := y'
    rw [(show y' = y by rfl)]
    clear * -

    -- we want to prove (x + y) / (x ^ 4 + y ^ 4 + 6) ≤ 1 / 4,
    -- so we can prove by x + y ≤ (x ^ 4 + y ^ 4 + 6) / 4
    -- so we cam prove x ≤ (x ^ 4 + 3) / 4 and y ≤ (y ^ 4 + 3) / 4
  
    -- here we prove that x ≤ 3 / 4 + x ^ 4 * (1 / 4) first
    have h1 (x: ℝ) : x ≤ 3 / 4 + x ^ 4 * (1 / 4) := by
      have h0 : x ^ 4 - 4 * x + 3 = (x - 1) ^ 2 * ((x+1) ^ 2 + 2) := by ring_nf
      replace h0 : 0 ≤ x ^ 4 - 4 * x + 3 := by
        rw [h0]
        exact mul_nonneg (sq_nonneg (x - 1)) (add_nonneg (sq_nonneg (x + 1)) ( by norm_num))
      have h1 : 3 / 4 + x ^ 4 * (1 / 4) - x = (x ^ 4 - 4 * x + 3) * (1 / 4) := by ring_nf
      have hn : 0 ≤ 3 / 4 + x ^ 4 * (1 / 4) - x := by
        rw [h1]
        exact mul_nonneg h0 (by norm_num)
      replace hn : 0 + x ≤ 3 / 4 + x ^ 4 * (1 / 4) - x + x := add_le_add_right hn x
      rw [zero_add, sub_add_cancel] at hn
      exact hn


    have pow4_nonneg {x: ℝ}: 0 ≤ x ^ 4 := by
      have h1 : 4 = 2 * 2 := by norm_num
      rw [h1, pow_mul]
      exact sq_nonneg (x ^ 2)

    -- add up these inequalities: x ≤ (x ^ 4 + 3) / 4 and y ≤ (y ^ 4 + 3) / 4
    -- we get x + y ≤ (x ^ 4 + y ^ 4 + 6) / 4
    have x_add_y_le := add_le_add (h1 x) (h1 y)

    -- prove the denominator is positve.
    have b_pos : 0 + 0 + 0 < x ^ 4 + y ^ 4 + 6 := add_lt_add_of_le_of_lt (add_le_add pow4_nonneg pow4_nonneg) (show 0 < 6 by norm_num)
    simp at b_pos

    -- multiply (x ^ 4 + y ^ 4 + 6) to remove division operation
    rw [<-mul_le_mul_iff_of_pos_right b_pos, div_mul_cancel₀]

    -- prove the right side of x_add_y_le is exactly (x ^ 4 + y ^ 4 + 6).
    apply le_trans x_add_y_le
    apply le_of_eq
    ring_nf
    linarith only [b_pos]
