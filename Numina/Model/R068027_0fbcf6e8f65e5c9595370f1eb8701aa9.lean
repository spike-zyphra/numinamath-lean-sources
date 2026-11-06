import Mathlib

theorem algebra_313999 {f g : ℝ → ℝ} (hfg : ∀ x y, f (x - y) = f x * g y - g x * f y)
    (hf : f (-2) = f 1) (hf' : f 1 ≠ 0) : g 1 + g (-1) = -1 := by
  have f0 : f 0 = 0 := by
    specialize hfg 0 0
    norm_num at hfg
    linarith

  have g0 : g 0 = 1 := by
    specialize hfg 1 0
    have eq1 : f (1 - (0 : ℝ)) = f 1 * g 0 - g 1 * f 0 := hfg
    simp [f0] at eq1
    have eq2 : f 1 * (1 - g 0) = 0 := by 
      linarith

    cases (mul_eq_zero.mp eq2) with
    | inl h1 =>
      exfalso
      exact hf' (by linarith)
    | inr h2 =>
      linarith

  have eqf1 : f (-1) = - f 1 := by 
    specialize hfg 0 1 
    simp [f0, g0] at hfg
    linarith

  have eq1 : f (-2) = f (-1) * g 1 - g (-1) * f 1 := by
    specialize hfg (-1) 1
    -- Use norm_num to simplify arithmetic expressions
    norm_num at hfg ⊢
    exact hfg
  -- Substituting f (-2) = f 1 and f (-1) = -f 1 into the equation
  rw [show f (-2) = f 1 by linarith [hf], show f (-1) = - f 1 by linarith [eqf1]] at eq1

  have h : f 1 * (1 + g 1 + g (-1)) = 0 := by
    linarith

  cases (mul_eq_zero.mp h) with
  | inl h1 => 
      exfalso
      exact hf' h1
  | inr h2 => 
      linarith
  all_goals linarith