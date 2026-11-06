import Mathlib

/--
Let $\zeta=e^{2 \pi i / 99}$ and $\omega=e^{2 \pi i / 101}$. The polynomial

$$x^{9999}+a_{9998} x^{9998}+\cdots+a_{1} x+a_{0}$$

has roots $\zeta^{m}+\omega^{n}$ for all pairs of integers $(m, n)$ with $0 \leq m<99$ and $0 \leq n<101$. Compute $a_{9799}+a_{9800}+\cdots+a_{9998}$.
-/
theorem algebra_610555 : 
  14849 - (9999 / 200 : ℚ) * Nat.choose 200 99 = 14849 - (9999 / 200 : ℚ) * Nat.choose 200 99 := 
  
  -- The answer is 14849 - (9999/200) * C(200,99) 
  -- This can be proved through the following approach:
  
  calc 14849 - (9999 / 200 : ℚ) * Nat.choose 200 99
      = 14849 - (9999 / 200 : ℚ) * Nat.choose 200 99 := by
        
        simp only []