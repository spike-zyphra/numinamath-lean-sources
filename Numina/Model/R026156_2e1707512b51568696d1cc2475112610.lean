import Mathlib

theorem algebra_1869 (f : ℕ → ℕ) : (∀ n, f n + √(f n + n ^ 2) = (3 * n + 2)) ↔ ∀ n, f n = 2 * n + 1 := by
  constructor
  · -- Assume $\forall n, f n + \sqrt{f n + n ^ 2} = 3 * n + 2$ then $\forall n, f n = 2 * n + 1$
    intro h
    intro n
    have eq1 := h n
    have h1 : (f n : ℝ) + Real.sqrt ((f n : ℝ) + (n : ℝ) ^ 2) = (3 * (n : ℝ) + 2) := by
      simpa using eq1
    have h2 : Real.sqrt ((f n : ℝ) + (n : ℝ) ^ 2) ^ 2 = (f n : ℝ) + (n : ℝ) ^ 2 := by
      rw [Real.sq_sqrt]
      have h3 : (0 : ℝ) ≤ (f n : ℝ) + (n : ℝ) ^ 2 := by
        positivity
      linarith
    have h_eq : Real.sqrt ((f n : ℝ) + (n : ℝ) ^ 2) = (n + 1 : ℝ) := by
      nlinarith [sq_nonneg (Real.sqrt ((f n : ℝ) + (n : ℝ) ^ 2) - (n + 1 : ℝ)), 
                  Real.sqrt_nonneg ((f n : ℝ) + (n : ℝ) ^ 2), 
                  Real.sq_sqrt (show 0 ≤ (f n : ℝ) + (n : ℝ) ^ 2 by positivity), 
                  h1, h2, 
                  sq_nonneg ((f n : ℝ) - (2 * (n : ℝ) + 1))
                ]
    have eq2 : (f n : ℝ) = (2 * (n : ℝ) + 1) := by
      linarith [h_eq, h1]
    have eq3 : f n = 2 * n + 1 := by
      exact_mod_cast eq2
    exact_mod_cast eq3
  · -- Assume $\forall n, f n = 2 * n + 1$ then $\forall n, f n + \sqrt{f n + n ^ 2} = 3 * n + 2$
    intro hf
    intro n
    have eq1 : f n = 2 * n + 1 := hf n
    have h1 : (f n : ℝ) + Real.sqrt ((f n : ℝ) + (n : ℝ) ^ 2) = (3 * (n : ℝ) + 2) := by
      have eq1' : (f n : ℝ) = (2 * (n : ℝ) + 1) := by 
        exact_mod_cast eq1
      have h3 : (f n : ℝ) + (n : ℝ) ^ 2 = ((n + 1 : ℝ) ) ^ 2 := by 
        nlinarith [eq1']
      have h4 : Real.sqrt ((f n : ℝ) + (n : ℝ) ^ 2) = (n + 1 : ℝ) := by 
        rw [h3]
        rw [Real.sqrt_sq (by positivity)]
      nlinarith [eq1', h4]
    exact_mod_cast h1