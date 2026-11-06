import Mathlib

open Real Set
open scoped BigOperators

/- Problem 10.1. Solve the inequality


$$

\sqrt{x^{2}-1}+\sqrt{2 x^{2}-3}+x \sqrt{3}>0

$$


Peter Boyvalenkov -/
theorem inequalities_296033 (x : ℝ) :
    0 ≤ x^2 - 1 ∧ 0 ≤ 2 * x^2 - 3 ∧ √ (x^2 - 1) + √ (2 * x^2 - 3) + x * √ 3 > 0 ↔
    x < -√ (5 + √ 33) / 2 ∨ x ≥ √ 6 / 2 := by
  -- we prove some positive facts that will be used in other proofs later
  have h₁ : 0 < √6 / 2 := by positivity
  have h₂ : 0 < √3 := by positivity
  constructor
  -- first prove left to right
  . rintro ⟨hx₁, hx₂, hx₃⟩
    -- fromx hx₂ we get following bound, we can cancel the square to get two branches one for negative, one for positive
    have hx₄ : (√6 / 2)^2 ≤ x^2 := by
      ring_nf; simp;  linarith
    replace hx₄ := sq_le_sq.mp hx₄
    rw [abs_of_nonneg (by linarith)] at hx₄
    obtain h | h := le_abs.mp hx₄
    -- the positive branch is same as one branch of goal
    . right
      assumption
    -- for negative branch
    . left
      have hx₅ : x < 0 := by linarith
      -- put the positive parts in two side and square
      replace hx₃ : (- x * √3)^2 <  (√(x ^ 2 - 1) + √(2 * x ^ 2 - 3))^2 := by
        gcongr
        . nlinarith
        . linarith
      ring_nf at hx₃ hx₁ hx₂
      simp [hx₁, hx₂] at hx₃
      -- square the resultant expression again
      replace hx₃ : 2^2 < (√(-1 + x ^ 2) * √(-3 + x ^ 2 * 2))^2 := by
        gcongr
        linarith
      ring_nf at hx₃
      simp [hx₁, hx₂] at hx₃
      ring_nf at hx₃
      -- express the resultant expression using square of a linear expression
      replace hx₃ : 33 < (4 * x^2 - 5)^2 := by linarith only [hx₃]
      rw [show 33 = (√33)^2 by simp] at hx₃
      -- square root and then again square root, but note x is negative, so wil lhave to take -x as root
      replace hx₃ := sq_lt_sq₀ (by positivity) (by linarith) |>.mp hx₃
      replace hx₃ : (5 + √33)/4 < (-x)^2 := by linarith
      -- finally this is the required goal
      have : (5 + √33)/4 = (√(5 + √33)/2) ^ 2 := by
        rw [div_pow]
        norm_num
        rw [Real.sq_sqrt]
        positivity
      rw [this] at hx₃
      replace hx₃ := sq_lt_sq₀ (by positivity) (by linarith) |>.mp hx₃
      linarith
  . rintro h
    obtain h | h := h
    -- if negative branch is true then first prove x ≤ -√6/2
    . have :  √6 / 2 ≤ √(5 + √33) / 2 := by
        rw [show (6:ℝ) = 5 + 1 by norm_num]
        gcongr
        simp
      have : √6 / 2 ≤ -x := by linarith
      -- hence we get a bound of x^2, this will help in the first two simpler goals
      have : (√6 / 2)^2 ≤ (-x)^2 := by gcongr
      ring_nf at this; simp at this
      and_intros
      . linarith
      . linarith
        -- for the complicated goal, we will go in reverse, first square
      . have : (√(5 + √33) / 2)^2 < (-x)^2 := by
          gcongr
          linarith
        ring_nf at this
        simp [show  0 ≤ 5 + √33 by positivity] at this
        -- then putting √33 in one side, square again
        have : (√33)^2 < (4*x^2 - 5)^2 := by
          gcongr
          linarith
        simp at this
        -- resprsent following expression which was gotten midway during left to right proof
        have : 2 < √(-1 + x ^ 2) * √(-3 + x ^ 2 * 2) := by
          nth_rw 1 [show 2 = √ (2^2) by simp]
          rw [← Real.sqrt_mul (by linarith)]
          simp [-sqrt_sq]
          linarith
        -- now express the final target's squared version using last fact
        have : (- x * √3)^2 <  (√(x ^ 2 - 1) + √(2 * x ^ 2 - 3))^2 := by
          ring_nf
          simp
          rw [Real.sq_sqrt (by linarith)]
          rw [Real.sq_sqrt (by linarith)]
          linarith
        -- cancelling the square we're done
        rw [sq_lt_sq₀ (by nlinarith) (by positivity)] at this
        linarith
      -- for positive branch as usual establish lower bound of x^2
    . have : (√6/2)^2 ≤ x^2 := by gcongr
      ring_nf at this
      simp at this
      -- the first two goal proved using the square's lower bound, for other goal, due to x being positive, that is also easily proved
      and_intros
      . linarith
      . linarith
      . apply add_pos_of_nonneg_of_pos
        . positivity
        . nlinarith