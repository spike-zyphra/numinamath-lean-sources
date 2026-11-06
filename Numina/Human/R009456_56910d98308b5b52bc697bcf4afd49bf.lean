import Mathlib

/- $w,x,y,z$ are real numbers such that
$$
w + x + y + z = 5
2w + 4x + 8y + 16z = 7
3w + 9x + 27y + 81z = 11
4w + 16x + 64y + 256z = 1
$$
What is the value of $5w+25x+125y+625z$?
-/
theorem algebra_608766 (w x y z : ℝ)
    (h₀ : w + x + y + z = 5)
    (h₁ : 2*w+4*x+8*y+16*z=7)
    (h₂ : 3*w+9*x+27*y+81*z=11)
    (h₃ : 4*w+16*x+64*y+256*z=1):
    5*w+25*x+125*y+625*z=-60 := by
  -- by solving the linear system, we can get the values of w, x, y, z.
  -- then ths result is direct.
  linarith [h₀, h₁, h₂, h₃]
