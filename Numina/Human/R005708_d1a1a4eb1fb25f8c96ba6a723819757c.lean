import Mathlib
open Real
open Complex

/-
Let $x$ and $y$ be complex numbers such that $x+y=\sqrt{20}$ and $x^{2}+y^{2}=15$. Compute $|x-y|$.
-/
theorem algebra_609525 {x y : ℂ} (h0 : x + y = √20) (h1 : x ^ 2 + y ^ 2 = 15) : abs (x - y) = √10 := by

  -- The core identity to use x+y and x^2 + y^2 to express (x-y)
  have h: (x-y)^2 + (x+y)^2 = 2*(x^2+y^2) := by ring
  rw [h0, h1] at h
  norm_cast at h
  norm_num at h

  -- Simplify the equation by rw the value of x+y and x^2 + y^2
  have h' : (x-y)^2 = 10 := by
    calc
      _ = (x-y)^2 + 20 - 20 := by ring
      _ = 30 - 20 := by rw [h]
      _ = 10 := by norm_num

  -- Change variable to simplify process.
  let z:ℂ := x-y

  have hz: z^2 = 10 := by unfold z; exact h'

  -- Since the x,y are complex numbers, we must take abs to it then take square root.

  -- |z^2| = |z|^2
  have hzabs: abs (z^2) = (abs z)^2 := by
    rw [abs_pow]
  have zabs: abs (z^2) = 10 := by
    rw [hz]
    rw [abs_def]
    simp
  rw [hzabs] at zabs

  -- Take square root on both sides.
  have hp: abs z = sqrt 10 := by
    have : abs z ≥ 0 := by
      rw [abs_def]
      simp
    calc
      _ = sqrt ((abs z) * (abs z)):= by
        rw [sqrt_mul_self]
        positivity
      _ = sqrt (abs z ^ 2) := by simp
      _ = sqrt (10) := by rw [zabs]

  -- write back the z to x-y and proof the final goal.
  have : abs (x-y) = abs z := by
    unfold z
    linarith
  rw [this]
  exact hp
    

  
