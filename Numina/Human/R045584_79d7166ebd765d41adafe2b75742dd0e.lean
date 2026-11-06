import Mathlib

/- Find the greatest $a$ such that $\frac{7\sqrt{(2a)^2+(1)^2}-4a^2-1}{\sqrt{1+4a^2}+3}=2$. -/
theorem algebra_15054 :
    IsGreatest {a | (7 * √((2 * a) ^ 2 + 1) - 4 * a ^ 2 - 1) / (√(1 + 4 * a ^ 2) + 3) = 2} √2 := by
  -- Two goals:
  -- 1. Show that √2 can be achieved
  -- 2. Show that no larger value can be achieved
  constructor
  . -- Just plug in a = √2 into the equation
    simp
    ring_nf
    norm_num
    -- Simplify the equation using √9 = 3
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    simp
    norm_num
  . -- We prove a ≤ √2
    intro a ha
    simp at ha

    -- We let x = 4a^2 + 1
    -- It suffices to prove that x ≤ 9
    suffices h : 4 * a ^ 2 + 1 ≤ 9 by
      replace h : a ^ 2 ≤ 2 := by linarith
      rw [show 2 = √2 ^ 2 by simp] at h
      nlinarith [show √2 > 0 by simp]

    -- Write the equation in terms of x
    replace ha : (7 * √(4 * a ^ 2 + 1) - (4 * a ^ 2 + 1)) / (√(4 * a ^ 2 + 1) + 3) = 2 := by
      ring_nf at ha ⊢
      exact ha
    -- x is positive
    have xpos : 0 < 4 * a ^ 2 + 1 := by
      linarith only [sq_nonneg a]
    -- Substitute x = 4a^2 + 1
    generalize 4 * a ^ 2 + 1 = x at ha xpos

    -- We let y = √x
    -- It suffices to prove that y ≤ 3
    suffices h : √x ≤ 3 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
      exact (Real.sqrt_le_left (by norm_num)).1 h

    -- Write the equation in terms of y
    nth_rw 2 [← show √x ^ 2 = x from Real.sq_sqrt (le_of_lt xpos)] at ha
    rw [← Real.sqrt_pos] at xpos

    -- Substitute y = √x
    generalize √x = y at ha xpos

    -- Simplify the equation and we get a quadratic equation
    field_simp at ha
    by_contra! h
    nlinarith
