import Mathlib

theorem algebra_608766 (w x y z : ℝ)
    (h₀ : w + x + y + z = 5)
    (h₁ : 2*w+4*x+8*y+16*z=7)
    (h₂ : 3*w+9*x+27*y+81*z=11)
    (h₃ : 4*w+16*x+64*y+256*z=1):
    5*w+25*x+125*y+625*z=-60 := by
  linarith