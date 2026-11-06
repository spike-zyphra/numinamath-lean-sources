import Mathlib

theorem algebra_166402 {x y : ℝ} (h : x^2 + 2 * y + Real.sqrt (x^2 + 2 * y + 1) = 1 ∧ 2 * x + y = 2) :
    x = 2 ∧ y = -2 := by 
  rcases h with ⟨h1, h2⟩
  have eq1 : y = 2 - 2 * x := by
    linarith 
  have eq2 : x^2 + 2 * y + 1 = (x - 2)^2 + 1 := by
    rw [eq1]
    nlinarith
  have eq3 : Real.sqrt (x^2 + 2 * y + 1) = Real.sqrt ((x - 2)^2 + 1) := by
    rw [eq2]
  have eq4 : x^2 + 2 * y = (x - 2)^2 := by 
    rw [eq1]
    nlinarith 
  have h3 : (x - 2)^2 + Real.sqrt ((x - 2)^2 + 1) = 1 := by
    nlinarith [h1, eq3, eq4]
  -- Solve A + real.sqrt(A + 1) = 1.
  -- This implies that $A \geq 0$ and $\sqrt{A + 1} = 1 - A$.
  -- Squaring both sides: $(1 - A)^2 = A + 1$
  -- Expanding: $1 - 2 * A + A^2 = A + 1$
  -- Simplifies to: $A^2 - 3 * A = 0$
  -- Factor: $A * (A - 3) = 0$
  -- Since A = (x - 2)^2.
  have h4 : Real.sqrt ((x - 2)^2 + 1) = 1 - (x - 2)^2 := by 
    nlinarith [h3]
  have h5 : (1 - (x - 2)^2) ^ 2 = (x - 2)^2 + 1 := by 
    calc
      (1 - (x - 2)^2) ^ 2 = (Real.sqrt ((x - 2)^2 + 1)) ^ 2 := by 
        rw [h4]
      _ = (x - 2)^2 + 1 := by 
        rw [Real.sq_sqrt]
        positivity 
  have h6 : (x - 2)^2 * ((x - 2)^2 - 3) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case (x - 2)^2 = 0
    have h8 : x - 2 = 0 := by
      apply pow_eq_zero 
      exact h7 
    have hx : x = 2 := by 
      linarith 
    have hy : y = -2 := by 
      rw [eq1] 
      linarith 
    exact ⟨hx, hy⟩ 
  · -- Case (x - 2)^2 - 3 = 0 
    -- This means (x - 2)^2 = 3, so A = 3.
    -- Check if with A = 3, Real.sqrt(A + 1) = 1 - A.
    -- i.e. Real.sqrt(4) = -2 which is false because Real.sqrt(4) = 2.
    -- Therefore this solves algebraically but is contradicts positivity of square roots.
    -- Therefore, can be excluded.
    nlinarith [Real.sqrt_nonneg ((x - 2) ^ 2 + 1), Real.sq_sqrt (show (x - 2) ^ 2 + 1 ≥ 0 by positivity)]