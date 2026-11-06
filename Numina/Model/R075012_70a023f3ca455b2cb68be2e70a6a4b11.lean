import Mathlib

theorem algebra_306998 (x : ℝ) :
    Real.sin (2 * x) = 2 * Real.sin x * Real.cos x ∧
    Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 := by 
  constructor 
  · -- Proof of sine double angle
    rw [Real.sin_two_mul]
  · -- Proof of cosine double angle 
    have h1 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by 
      exact Real.cos_two_mul x
    -- We need to convert this expression to the desired form
    have h2 : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 := by 
      -- Using the expression from the lemma and algebra
      have h3 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := h1 
      have h4 : 2 * Real.cos x ^ 2 - 1 = Real.cos x ^ 2 - Real.sin x ^ 2 := by 
        have h5 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
          have h6 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by 
            exact Real.cos_sq_add_sin_sq x
          linarith 
        rw [h5]
        ring 
      -- Now we can use the equality derived 
      linarith 
    -- Therefore, it is sufficient to conclude 
    exact h2