import Mathlib

/-
Problem

Given the system of equations in terms of $x$ and $y$: $\left\{\begin{array}{l}x+2y-6=0\\ x-2y+mx+5=0\end{array}\right.$, if the solutions of the system have $x$ as an integer and $m$ as an integer, then the value of $m$ is ______.
-/

theorem algebra_9056 {x y m : ℤ} (h1 : x + 2 * y - 6 = 0) (h2 : x - 2 * y + m * x + 5 = 0) :
  m = -1 ∨ m = -3 := by 
  have h3 : x * (2 + m) = 1 := by
    nlinarith
  have h4 : x = 1 ∨ x = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h3
  cases h4 with
  | inl hx1 =>
    have hm1 : m = -1 := by 
      rw [hx1] at h3 
      linarith 
    left 
    exact hm1 
  | inr hx1 => 
    have hm3 : m = -3 := by 
      rw [hx1] at h3 
      linarith 
    right 
    exact hm3