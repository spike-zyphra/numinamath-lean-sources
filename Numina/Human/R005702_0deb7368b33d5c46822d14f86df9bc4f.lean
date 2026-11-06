import Mathlib

open Complex

/-
Let $z$ be a complex number such that
$|z|=1$ and $|z-1.45|=1.05$.
Compute the real part of $z$.
-/

theorem algebra_609495 (z : ℂ) (hz1 : ‖z‖ = 1) (hz2 : ‖z - 1.45‖ = 1.05)
    : z.re = 20 / 29 := by
  let w := z - 1.45
  have wre : w.re = z.re - 1.45 := by rfl
  have wim : w.im = z.im        := by simp [w]; rfl

  -- Working with the square of the norm is much easier.
  have nzsq : normSq z = 1 := Real.sqrt_eq_one.mp hz1
  have nwsq : normSq w = 1.05^2 := by simp [w]; rw [normSq_eq_norm_sq, hz2]

  -- Let's name real and imaginary parts to work more easily.
  obtain ⟨x, y⟩ := z
  obtain ⟨s, t⟩ := w
  have xs : s = x - 1.45 := wre
  have yt : y = t := by linarith

  -- Rewrite hz1 so that $x^2 + y^2 = 1$.
  have eqn1 : x*x + y*y = 1 := by rw [normSq_mk] at nzsq; exact nzsq

  -- Rewrite hz2 so that $s^2 + t^2 = 1.05^2$.
  have eqn2 : s*s + t*t = 1.05^2 := by rw [normSq_mk] at nwsq; exact nwsq

  -- Replace s,t with x,y.
  have eqn3 : (x-1.45)*(x-1.45) + y*y = 1.05^2 := by simp_all

  -- Expand this equation:
  have eqn4 : x*x - 2.9*x + 1.45^2 + y*y = 1.05^2 := by linarith

  -- Subtract two equations to cancel $x^2, y^2$ to get $-2.9x + 1.45^2 = 1.05^2 - 1$.
  have eqn5 : -2.9*x + 1.45^2 = 1.05^2 - 1 := by linarith

  -- Solve to get $x = \frac{1.05^2 - 1 - 1.45^2}{-2.9} = 20/29$
  linarith
