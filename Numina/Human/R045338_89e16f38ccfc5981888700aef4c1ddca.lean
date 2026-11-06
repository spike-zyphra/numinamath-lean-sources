import Mathlib

open Real Set
open scoped BigOperators

/- 10. (1st "Hope Cup" Senior High School Grade 2nd Test, Question 3) $f$ is a one-to-one mapping from $\mathbf{R} \rightarrow \mathbf{R}$, and the function $y=f(x)$ is strictly increasing. The solution set of the inequality $x > f(x)$ is $P$, and the solution set of the inequality $x > f[f(x)]$ is $Q$. Then ( )
A. $P \ni Q$
B. $P=Q$
C. $Q \varsubsetneqq P$
D. $P \varsubsetneqq Q$ and $Q \varsubsetneqq P$ -/
theorem inequalities_254329 {f : ℝ → ℝ}
    (hf : Function.Injective f) (hinc : StrictMono f)
    (P Q : Set ℝ) (hP : P = {x | x > f x}) (hQ : Q = {x | x > f (f x)}) :
    P = Q := by
  -- we'll prove P ⊆ Q and Q ⊆ P
  ext x
  constructor <;> (rintro h; rw[hP, hQ] at *; simp at *)
  -- if f x < x then f (f x) < f x, combining this with hypothesis gives target
  . have : f (f x) < f x := hinc h
    linarith
  -- we'll prove f x < x by contradiction, if x ≤ f x then f x ≤ f (f x), this with hypotheiss proves contradiction
  . apply lt_of_not_le
    by_contra h'
    have : f x ≤ f (f x) := StrictMono.monotone hinc h'
    linarith