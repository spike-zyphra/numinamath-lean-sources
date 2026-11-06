import Mathlib

theorem algebra_323007 {a : ℝ} (ha : a = Real.sqrt 3 - 1) :
    a ^ 2012 + 2 * a ^ 2011 - 2 * a ^ 2010 = 0 := by 
  have h1 : a + 1 = Real.sqrt 3 := by 
    rw [ha]
    ring
  -- Square both sides: $(a + 1)^2 = (\sqrt{3})^2$ which gives $a^2 + 2 a + 1 = 3$.
  have h2 : (a + 1) ^ 2 = 3 := by 
    rw [h1]
    have h3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    linarith
  -- Expanding left side: $a^2 + 2 a + 1 = 3$. Therefore $a^2 + 2 a = 2$.
  have h4 : a ^ 2 + 2 * a = 2 := by 
    have h5 : (a + 1) ^ 2 = a^2 + 2 * a + 1 := by ring
    rw [h5] at h2
    linarith
  -- Therefore $a^2 + 2 a - 2 = 0$
  have eq1 : a ^ 2012 + 2 * a ^ 2011 - 2 * a ^ 2010 = a ^ 2010 * (a ^ 2 + 2 * a - 2) := by 
    ring
  -- Now we need to rewrite $a^2 + 2a - 2 = 0$ into the equation
  rw [eq1]
  have h6 : a ^ 2 + 2 * a - 2 = 0 := by
    have h7 : a ^ 2 + 2 * a = 2 := h4
    linarith
  -- Multiply by a^{2010}: a^{2010}(0) = 0
  rw [h6]
  <;> ring