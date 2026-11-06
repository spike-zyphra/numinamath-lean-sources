import Mathlib
/- 11. Given $\frac{x y}{x+y}=2, \frac{x z}{x+z}=3, \frac{y z}{y+z}=4$. Find the value of $7 x+5 y-2 z$. -/
theorem algebra_318667 {x y z : ℝ} (h1 : x * y / (x + y) = 2) (h2 : x * z / (x + z) = 3) (h3 : y * z / (y + z) = 4) :
7 * x + 5 * y - 2 * z = 0:= by
  -- Prove that x + y ≠ 0 by contradiction
  have g1 : x + y ≠ 0:= by
    by_contra H
    rw [H] at h1
    simp at h1
  -- Prove that x + z ≠ 0 by contradiction
  have g2 : x + z ≠ 0:= by
    by_contra H
    rw [H] at h2
    simp at h2
  -- Prove that y + z ≠ 0 by contradiction
  have g3 : y + z ≠ 0:= by
    by_contra H
    rw [H] at h3
    simp at h3
  -- Prove that x ≠ 0 by contradiction
  have g4 : x ≠ 0:= by
    by_contra H
    rw [H] at h1
    simp at h1
  -- Prove that y ≠ 0 by contradiction
  have g5 : y ≠ 0:= by
    by_contra H
    rw [H] at h1
    simp at h1
  -- Prove that z ≠ 0 by contradiction
  have g6 : z ≠ 0:= by
    by_contra H
    rw [H] at h2
    simp at h2
  -- Transform the first equation to 1/x + 1/y = 1/2
  replace h1 : 1 / x + 1 / y = 1 / 2:= by
    field_simp at h1 ⊢
    linarith
  -- Transform the second equation to 1/x + 1/z = 1/3
  replace h2 : 1 / x + 1 / z = 1 / 3:= by
    field_simp at h2 ⊢
    linarith
  -- Transform the third equation to 1/y + 1/z = 1/4
  replace h3 : 1 / y + 1 / z = 1 / 4:= by
    field_simp at h3 ⊢
    linarith
  -- Solve the system of equations to get 1/x = 7/24
  replace h1 : 1 / x = 7 / 24:= by linarith
  -- Solve the system of equations to get 1/y = 5/24
  replace h2 : 1 / y = 5 / 24:= by linarith
  -- Solve the system of equations to get 1/z = 1/24
  replace h3 : 1 / z = 1 / 24:= by linarith
  -- Simplify the fractions
  field_simp at h1 h2 h3
  -- Complete the proof using linear arithmetic
  linarith
