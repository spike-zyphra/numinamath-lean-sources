import Mathlib

open Polynomial

/-If $A$ and $B$ are numbers such that the polynomial $x^{2017} + Ax + B$ is divisible by $(x + 1)^2$, what is the value of $B$?-/
theorem algebra_2904' {A B : ℝ} (h : (X + C 1)^2  ∣ X^2017 + C A * X + C B) : 
  B = -2016 := by
    obtain ⟨p, hp⟩ := h
    -- It is well known that $r$ is a double root of a polynomial $f(x)$ iff it is a
    -- root of $f(x)$ and  $f'(x)$ .  Let  $f(x) = x^{2017} + Ax + B$ .  We must have
    -- $f(-1) = B-A-1 = 0 \Rightarrow B = A+1$ .  
    have h1 : B = A + 1 := by 
      have : (X ^ 2017 + C A * X + C B).eval (-1) = ((X + C 1) ^ 2 * p).eval (-1) := by 
        simp [hp]
      simp at this
      nlinarith
    -- $f'(x) = 2017x^{2016} + A$ ,  so we
    -- must have  $f'(-1) = 2017 + A = 0 \Rightarrow A = -2017 \Rightarrow B=
    -- \boxed{-2016}$ .
    apply_fun (Polynomial.derivative · ) at hp 
    simp [Polynomial.derivative_pow] at hp
    have : (C 2017 * X ^ 2016 + C A).eval (-1) = (C 2 * (X + 1) * p + (X + 1) ^ 2 * derivative p).eval (-1) := by simp [hp]
    simp at this
    nlinarith
