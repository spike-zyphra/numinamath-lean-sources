import Mathlib
open Real

/- If for any three distinct numbers a, b, and c we define f(a,b,c)=(c+a)/(c-b) then f(1,-2, -3) is
(A) -2  (B) -2/5 (C) -1/4 (D) 2/5 (E) 2 -/
theorem algebra_96968 (f : ℝ → ℝ → ℝ → ℝ) (hf : ∀ a b c, f a b c = (c + a) / (c - b)) :
f 1 (-2) (-3) = 2 := by
  -- solve by calculation
rw [hf]
norm_num