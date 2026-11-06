import Mathlib

open Real Set
open scoped BigOperators

/-
The range of the function $f(x) = \log_{2}(-x^{2} - 2x + 3)$ is.
-/
theorem algebra_9245 : range (fun (x : {x : ℝ // 0 < -x^2 - 2*x + 3}) ↦ logb 2 (-x.val^2 - 2*x.val + 3)) = {y | y ≤ 2} := by
  -- Simplify the goal by unfolding the definition of `range`
  dsimp [range]
  -- Prove the equality of sets by proving the double inclusion
  rw [Set.ext_iff]
  intro x
  constructor <;> intro h
  · -- Prove the forward inclusion: if `x` is in the range, then `x ≤ 2`
    simp_all
    -- Obtain a witness `y` such that `logb 2 (-y^2 - 2*y + 3) = x`
    obtain ⟨y, hy, h'⟩ := h
    rw [← h']
    -- Prove that `logb 2 4 = 2`
    have : logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by linarith, Real.logb_rpow (by linarith) (by linarith)]
    -- Rewrite using the above fact and prove that `logb 2 (-y^2 - 2*y + 3) ≤ logb 2 4`
    nth_rw 3 [← this]
    rw [Real.logb_le_logb (by linarith) hy (by linarith)]
    -- Prove that `0 ≤ y^2 + 2*y + 1` to conclude
    suffices h' : 0 ≤ y^2 + 2*y + 1 by linarith
    rw [show y^2 + 2*y + 1 = (y + 1)^2 by ring]
    apply sq_nonneg
  · -- Prove the backward inclusion: if `x ≤ 2`, then `x` is in the range
    simp_all
    -- Use `√(4 - 2^x) - 1` as a witness
    use √(4 - 2^x) - 1
    rw [sub_sq,sq_sqrt]
    ring_nf
    norm_num
    -- Obviously, we have `2^x > 0`
    exact Real.rpow_pos_of_pos (by linarith) x
    -- Prove that `2^x ≤ 4` to conclude
    suffices h' : (2 : ℝ) ^ x ≤ 4 by norm_num [h']
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
    exact (Real.rpow_le_rpow_left_iff (show 1 < (2 : ℝ) by norm_num)).mpr h
