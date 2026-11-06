import Mathlib

open Real

/- 求解一元二次方程$x^2=a, a\geq 0$。-/
lemma Real.sq_eq {a : ℝ} (ha : 0 ≤ a) {x : ℝ} : x ^ 2 = a ↔ x = sqrt a ∨ x = -sqrt a := by
  constructor
  . intro h
    apply_fun sqrt at h
    rw [pow_two, sqrt_mul_self_eq_abs] at h
    rcases abs_choice x with hx | hx
    . left; rwa [hx] at h
    . right; rw [hx] at h; linear_combination -h
  intro h; rcases h with h | h <;> rw [h] <;> simp [sq_sqrt ha]

/- 奇偶分析，偶数不等于1-/
lemma two_mul_ne_one (k : ℤ) : 2 * k ≠ 1 := by
  intro h
  have : ¬ Even (1 : ℤ) := Int.not_even_one
  have : Even (1 : ℤ) := h ▸ ⟨k, two_mul k⟩
  contradiction

/- Find the sum of all real roots of the equation
$$
\sin \left(\pi\left(x^{2}-x+1\right)\right)=\sin (\pi(x-1))
$$
that belong to the interval $[0, 2]$.-/
theorem algebra_4029 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 2) : sin (π * (x ^ 2 - x + 1)) = sin (π * (x - 1)) ↔
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = sqrt 3 := by
  rw [sin_eq_sin_iff]
  constructor
  rintro ⟨k, h⟩
  rcases h with h | h
  -- 方程1 π(x-1)=2kπ+π(x^2-x+1)
  conv_rhs at h => rw [mul_comm _ π, ← mul_add]
  rw [mul_right_inj' pi_ne_zero] at h -- 消去π
  have : (x - 1) ^ 2 = -2 * k - 1 := by -- 配方
    rw [← add_zero ((x - 1) ^ 2), ← sub_eq_zero_of_eq h]; ring
  have hk : (0 : ℝ) ≤ -2 * k - 1 := by
    rw [← this]; apply sq_nonneg
  rw [Real.sq_eq hk] at this
  rcases this with hsol | hsol
  -- 方程1解1 x=1+√(-2k-1)
  rw [sub_eq_iff_eq_add] at hsol
  rw [hsol] at hx
  rcases hx with ⟨hx1, hx2⟩
  have := add_le_add_right hx2 (-1)
  rw [add_assoc, add_neg_cancel, add_zero, show 2 + -1 = (1 : ℝ) by ring] at this
  conv_rhs at this => rw [show 1 = sqrt 1 by norm_num]
  rw [sqrt_le_sqrt_iff <| show 0 ≤ 1 by norm_num] at this
  norm_cast at this hk
  simp at hk this
  interval_cases h2k : -(2 * k)
  . have : -(2 * k) ≠ 1 := by
      rw [show -(2 * k) = 2 * (-k) by ring]
      exact two_mul_ne_one (-k)
    contradiction
  -- 解得 k=-1
  rw [neg_eq_iff_eq_neg, show -2 = 2 * -1 by ring, mul_right_inj' (by norm_num)] at h2k
  rw [h2k] at hsol
  simp at hsol
  rw [show 2 - 1 = (1 : ℝ) by ring, sqrt_one] at hsol
  right; right; left; rw [hsol]; norm_num -- 代入得 x=2
  -- 方程1解2 x=1-√(-2k-1)
  rw [sub_eq_iff_eq_add] at hsol
  rw [hsol] at hx
  rcases hx with ⟨hx1, hx2⟩
  have := add_le_add_right hx1 <| sqrt <| -2 * k - 1
  simp at this hk
  rw [show 1 + 1 = (2 : ℝ) by ring] at this
  norm_cast at this hk
  interval_cases h2k : -(2 * k)
  . have : -(2 * k) ≠ 1 := by
      rw [show -(2 * k) = 2 * (-k) by ring]
      exact two_mul_ne_one (-k)
    contradiction
  -- 解得 k=-1
  rw [neg_eq_iff_eq_neg, show -2 = 2 * -1 by ring, mul_right_inj' (by norm_num)] at h2k
  rw [h2k] at hsol
  simp at hsol
  rw [show 2 - 1 = (1 : ℝ) by ring, sqrt_one, show -1 + 1 = (0 : ℝ) by ring] at hsol
  left; assumption -- 代入得 x=0
  ----方程2 π(x-1)=(2k+1)π - π(x^2-x+1)
  conv_rhs at h => rw [mul_comm _ π, ← mul_sub]
  rw [mul_right_inj' pi_ne_zero] at h -- 消去π
  have : x ^ 2 = 2 * k + 1 := by -- 配方
    rw [← sub_zero (x ^ 2), ← sub_eq_zero_of_eq h]; ring
  have hk : (0 : ℝ) ≤ 2 * k + 1 := by
    rw [← this]; apply sq_nonneg
  rw [Real.sq_eq hk] at this
  rcases this with hsol | hsol
  -- 方程2解1 x=√(2k+1)
  rw [hsol] at hx
  rcases hx with ⟨hx1, hx2⟩
  replace hx2 := pow_le_pow_left (sqrt_nonneg _) hx2 2
  rw [pow_two, mul_self_sqrt hk, pow_two, show 2 * 2 = (4 : ℝ) by ring] at hx2
  norm_cast at hx2 hk
  interval_cases h2k : (2 * k + 1)
  . have : ¬Odd (0 : ℤ) := by norm_num
    have : Odd (0 : ℤ) := h2k ▸ ⟨k, rfl⟩
    contradiction
  conv_rhs at h2k => rw [show (1 : ℤ) = 2 * 0 + 1 by ring]
  -- 解得 k=0
  rw [add_right_cancel_iff, mul_right_inj' (by norm_num)] at h2k
  rw [h2k] at hsol
  simp at hsol
  right; left; assumption -- 代入得 x=1
  . have : ¬Odd (2 : ℤ) := by norm_num
    have : Odd (2 : ℤ) := h2k ▸ ⟨k, rfl⟩
    contradiction
  -- 解得 k=1
  rw [show (3 : ℤ) = 2 * 1 + 1 by ring, add_right_cancel_iff, mul_right_inj' (by norm_num)] at h2k
  rw [h2k] at hsol
  simp at hsol
  rw [show 2 + 1 = (3 : ℝ) by ring] at hsol
  right; right; right; assumption -- 代入得 x = √3
  . have : ¬Odd (4 : ℤ) := by rw [Int.not_odd_iff_even]; exact ⟨2, by norm_num⟩
    have : Odd (4 : ℤ) := by rw [← h2k]; exact ⟨k, rfl⟩
    contradiction
  -- 方程2解2 x=-√(2k+1)
  have : x < 0 := by
    rw [hsol, show (0 : ℝ) = -0 by ring, neg_lt_neg_iff, sqrt_pos]
    apply lt_of_le_of_ne hk
    norm_cast
    intro h
    apply two_mul_ne_one (k + 1)
    rw [← sub_zero (2 * (k + 1)), h]
    ring
  linarith
  -- 代入验算
  intro h
  rcases h with h | h | h | h <;> simp [h]
  use -1; left; ring
  use 0; right; ring
  use -1; left; ring
  use 1; right; ring
