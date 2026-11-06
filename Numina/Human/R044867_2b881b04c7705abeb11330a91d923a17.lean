import Mathlib

open Real
/-Real number a, b, c satisfy a ^ 2 + b ^ 2 + c ^ 2 = λ > 0, try to find the maximum value of 
f = min{(a-b) ^ 2,(b-c) ^ 2,(c-a) ^ 2}-/
theorem algebra_12119 (a b c lambda : ℝ) (h₀ : a^2 + b^2 + c^2 = lambda) (h₁ : lambda > 0) :
    min (min ((a - b)^2) ((b - c)^2)) ((c - a)^2) ≤ lambda / 2 := by
  by_cases h : (a - b) ^ 2 ≤ (b - c) ^ 2
  · -- If $(a - b)^2 \leq (b - c)^2$, then $\min\{(a - b)^2, (b - c)^2, (c - a)^2\} \leq (a - b)^2$
    have h1 : min ((a - b) ^ 2) ((b - c) ^ 2) = (a - b) ^ 2 := by
      apply min_eq_left
      nlinarith
    rw [h1]
    by_cases h' : (a - b) ^ 2 ≤ (c - a) ^ 2
    · -- If $(a - b)^2 \leq (c - a)^2$, then $\min\{(a - b)^2, (c - a)^2\} = (a - b)^2$
      have h2 : min ((a - b) ^ 2) ((c - a) ^ 2) = (a - b) ^ 2 := by
        apply min_eq_left
        nlinarith
      rw [h2]
      -- now we have eliminating the min function --
      -- the result can be obtained by using the above inequality --
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        h₀]
    · -- If $(a - b)^2 > (c - a)^2$, then $\min\{(a - b)^2, (c - a)^2\} = (c - a)^2$
      -- the rest is similar --
      have h2 : min ((a - b) ^ 2) ((c - a) ^ 2) = (c - a) ^ 2 := by
        apply min_eq_right
        nlinarith
      rw [h2]
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        h₀]
  · -- If $(a - b)^2 > (b - c)^2$, then $\min\{(a - b)^2, (b - c)^2, (c - a)^2\} \leq (b - c)^2$
    have h1 : min ((a - b) ^ 2) ((b - c) ^ 2) = (b - c) ^ 2 := by
      apply min_eq_right
      nlinarith
    rw [h1]
    by_cases h' : (b - c) ^ 2 ≤ (c - a) ^ 2
    · -- If $(b - c)^2 \leq (c - a)^2$, then $\min\{(b - c)^2, (c - a)^2\} = (b - c)^2$
      have h2 : min ((b - c) ^ 2) ((c - a) ^ 2) = (b - c) ^ 2 := by
        apply min_eq_left
        nlinarith
      rw [h2]
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        h₀]
    · -- If $(b - c)^2 > (c - a)^2$, then $\min\{(b - c)^2, (c - a)^2\} = (c - a)^2$
      have h2 : min ((b - c) ^ 2) ((c - a) ^ 2) = (c - a) ^ 2 := by
        apply min_eq_right
        nlinarith
      rw [h2]
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        h₀]