import Mathlib

/- Find all the solutions to
\[\sqrt{x} + 2 \sqrt{x^2 + 7x} + \sqrt{x + 7} = 35 - 2x.\]Enter all the solutions, separated by commas. -/
theorem algebra_15378 : {x | x ≥ 0 ∧ √x + 2 * √(x ^ 2 + 7 * x) + √(x + 7) = 35 - 2 * x} = {841/144} := by
  -- We prove both inclusions.
  ext x
  simp
  constructor
  . -- We show that if x satisfies the equation, then x = 841/144.
    intro ⟨xpos, hx⟩
    -- Set y = √x + √(x + 7).
    let y := √x + √(x + 7)
    -- We see y^2 = 2x + 7 + 2 √(x^2 + 7x) appears in the equation.
    have ysq : y^2 = 2 * x + 7 + 2 * √(x ^ 2 + 7 * x) := by
      simp only [y]
      ring_nf
      rw [Real.sq_sqrt xpos,
          Real.sq_sqrt (show 7 + x ≥ 0 by linarith),
          ← Real.sqrt_mul xpos]
      ring_nf
    -- We see that (y - 6)(y + 7) = 0.
    have hy : (y - 6) * (y + 7) = 0 := by
      calc _ = y^2 + y - 42 := by ring
           _ = (2 * x + 7 + 2 * √(x ^ 2 + 7 * x)) + (√x + √(x + 7)) - 42 := by rw [ysq]
           _ = _ := by linarith only [hx]
    -- y ≥ 0, so y = 6.
    replace hy : y = 6 := by
      nlinarith [show y ≥ 0 by positivity]
    simp only [y] at hy
    -- Move one square root to the other side.
    have h : √(x + 7) = 6 - √x := by
      linarith! only [hy]
    -- Square both sides.
    apply_fun (· ^ 2) at h
    ring_nf at h
    simp [show 7 + x ≥ 0 by linarith,
          xpos] at h
    -- We get the value of √x.
    replace h : √x = 29 / 12 := by
      linarith only [h]
    -- And then the value of x.
    apply_fun (· ^ 2) at h
    simp [xpos] at h
    norm_num at h
    exact h
  . -- We show that 841/144 satisfies the equation.
    rintro rfl
    -- Plug in the number and simplify.
    norm_num
    rw [show (841 : ℝ) = 29^2 by norm_num,
        show (144 : ℝ) = 12^2 by norm_num,
        show (1555009 : ℝ) = 1247^2 by norm_num,
        show (20736 : ℝ) = 144^2 by norm_num,
        show (1849 : ℝ) = 43^2 by norm_num]
    simp
    norm_num
