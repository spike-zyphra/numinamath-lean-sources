import Mathlib
open Mathlib
/--
A straight river that is $264$ meters wide flows from west to east at a rate of $14$ meters per minute. Melanie and Sherry sit on the south bank of the river with Melanie a distance of $D$ meters downstream from Sherry. Relative to the water, Melanie swims at $80$ meters per minute, and Sherry swims at $60$ meters per minute. At the same time, Melanie and Sherry begin swimming in straight lines to a point on the north bank of the river that is equidistant from their starting positions. The two women arrive at this point simultaneously. Find $D$.
-/
theorem algebra_25414
  (melanieDownstreamOffset riverWidth riverCurrent melanieSwimSpeed sherrySwimSpeed : ℝ)
  (hWidth : riverWidth = 264) (hCurrent : riverCurrent = 14) (hMelanie : melanieSwimSpeed = 80) (hSherry : sherrySwimSpeed = 60)
  (t : ℝ)
  (sherryRelativeVelocityX sherryRelativeVelocityY melanieRelativeVelocityX melanieRelativeVelocityY : ℝ)
  (h1 : Real.sqrt (sherryRelativeVelocityX^2 + sherryRelativeVelocityY^2) = sherrySwimSpeed)
  (h2 : Real.sqrt (melanieRelativeVelocityX^2 + melanieRelativeVelocityY^2) = melanieSwimSpeed)
  (h3 : t > 0)
  (h4 : (sherryRelativeVelocityX + riverCurrent) * t = melanieDownstreamOffset / 2)
  (h5 : (melanieRelativeVelocityX + riverCurrent) * t = - melanieDownstreamOffset / 2)
  (h6 : sherryRelativeVelocityY * t = riverWidth)
  (h7 : melanieRelativeVelocityY * t = riverWidth)
  : melanieDownstreamOffset = 550 := by
  -- From h6 and h7, we have sherryRelativeVelocityY * t = melanieRelativeVelocityY * t = riverWidth. Since t > 0, we can divide by t to get sherryRelativeVelocityY = melanieRelativeVelocityY.
  have step1 : sherryRelativeVelocityY = melanieRelativeVelocityY := by
    rw [←h7] at h6
    have st (a b c : ℝ) (h : a = b) : a / c = b / c := by rw [h]
    have := st _ _ t h6
    simp only [isUnit_iff_ne_zero, ne_eq, (by linarith : t ≠ 0), not_false_eq_true,
      IsUnit.mul_div_cancel_right] at this
    exact this
  -- Let's denote this common value as v_y.
  subst sherryRelativeVelocityY
  rename' melanieRelativeVelocityY => v_y
  -- So, v_y * t = riverWidth. Using hWidth, v_y * t = 264.
  have step2 : v_y * t = 264 := by linarith
  -- From h1 and h2, squaring both sides, we have: sherryRelativeVelocityX^2 + sherryRelativeVelocityY^2 = sherrySwimSpeed^2
  -- melanieRelativeVelocityX^2 + melanieRelativeVelocityY^2 = melanieSwimSpeed^2
  have st (a b : ℝ) (h : a = b) : a^2 = b^2 := by rw [h]
  have step3a := st _ _ h2
  have step3b := st _ _ h1
  simp only [(by clear * -; nlinarith : 0 ≤ melanieRelativeVelocityX ^ 2 + v_y ^ 2), Real.sq_sqrt,
    (by clear * -; nlinarith : 0 ≤ sherryRelativeVelocityX ^ 2 + v_y ^ 2)] at step3a step3b
  -- Thus, sherryRelativeVelocityX^2 = sherrySwimSpeed^2 - v_y^2
  -- melanieRelativeVelocityX^2 = melanieSwimSpeed^2 - v_y^2
  have step4a : sherryRelativeVelocityX^2 = sherrySwimSpeed^2 - v_y^2 := by linarith
  have step4b : melanieRelativeVelocityX^2 = melanieSwimSpeed^2 - v_y^2 := by linarith
  -- From h4 and h5, adding the two equations, we get:
  -- (sherryRelativeVelocityX + riverCurrent) * t + (melanieRelativeVelocityX + riverCurrent) * t = melanieDownstreamOffset / 2 - melanieDownstreamOffset / 2 = 0
  -- (sherryRelativeVelocityX + melanieRelativeVelocityX + 2 * riverCurrent) * t = 0
  have step5 : (sherryRelativeVelocityX + melanieRelativeVelocityX + 2 * riverCurrent) * t = 0 := by linarith
  -- Since t > 0 from h3, we must have:
  -- sherryRelativeVelocityX + melanieRelativeVelocityX + 2 * riverCurrent = 0
  -- melanieRelativeVelocityX = -sherryRelativeVelocityX - 2 * riverCurrent
  have step6 : melanieRelativeVelocityX = -sherryRelativeVelocityX - 2 * riverCurrent := by nlinarith
  have step7 : sherryRelativeVelocityX = 36 := by nlinarith
  -- From h4, melanieDownstreamOffset = 2 * (sherryRelativeVelocityX + riverCurrent) * t.
  have step8 : melanieDownstreamOffset = 2 * (sherryRelativeVelocityX + riverCurrent) * t := by linarith
  -- v_y^2 = sherrySwimSpeed^2 - sherryRelativeVelocityX^2 = 60^2 - 36^2 = 3600 - 1296 = 2304
  have step9 : v_y^2 = 2304 := by nlinarith
  have su (a b : ℝ) (h : a = b) : √a = √b := by rw [h]
  have step10 := su _ _ step9
  rw [(by norm_num : 2304 = (48 : ℝ)^2)] at step10
  simp only [(by nlinarith : 0 ≤ v_y), Real.sqrt_sq, Nat.ofNat_nonneg] at step10
  -- melanieDownstreamOffset = 2 * (sherryRelativeVelocityX + riverCurrent) * t = 2 * (36 + 14) * 5.5 = 2 * 50 * 5.5 = 550
  nlinarith