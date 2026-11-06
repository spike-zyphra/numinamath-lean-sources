import Mathlib

theorem algebra_296531 {f : ℝ → ℝ} (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (ha : 0 < a ∧ a < 1) (h : ∀ x y, x ≤ y → x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 →
    f ((x + y) / 2) = (1 - a ^ 2) * f x + a ^ 2 * f y) :
    a = Real.sqrt 2 / 2 := by

  -- First, compute f(1/2)
  have h12 : f (1 / 2) = a ^ 2 := by
    specialize h 0 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num [hf0, hf1] at h ⊢
    linarith

  -- Compute f(1/4)
  have h14 : f (1 / 4) = a ^ 4 := by
    specialize h 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    norm_num [hf0, h12] at h ⊢
    nlinarith

  -- Compute f(3/4)
  have h34 : f (3 / 4) = 2 * a ^ 2 - a ^ 4 := by 
    specialize h (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num [h12, hf1] at h ⊢
    nlinarith

  -- Equation involving f(1/2), f(1/4), f(3/4)
  have eq1 : f (1 / 2) = (1 - a ^ 2) * f (1 / 4) + a ^ 2 * f (3 / 4) := by
    specialize h (1 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  -- Substitute known values into eq1
  rw [h12, h14, h34] at eq1
  -- Now, solve the equation.
  -- Derive the polynomial factorization
  have h_eq2 : a ^ 2 * (2 * a ^ 4 - 3 * a ^ 2 + 1) = 0 := by
    nlinarith [eq1]
  cases' (mul_eq_zero.mp h_eq2) with h2 h3

  · -- Case where $a^2 = 0$, which contradicts $a > 0$.
    nlinarith [ha.1, ha.2]

  · -- Case where $2a^4 - 3a^2 + 1 = 0$.
    have h_eq3 : 2 * a ^ 4 - 3 * a ^ 2 + 1 = 0 := by
      nlinarith
    have h_eq4 : (2 * a ^ 2 - 1) * (a ^ 2 - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h_eq4) with h4 h5
    · -- Case where $2a^2 - 1 = 0$, so $a^2 = 1/2$.
      have ha2 : a ^ 2 = 1 / 2 := by
        linarith
      have : a = Real.sqrt (1 / 2) := by
        have hsqrt : a = Real.sqrt (a ^ 2) := by 
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_pos ha.1]
        rw [hsqrt, ha2]
      rw [this]
      have h3 : Real.sqrt (1 / (2 : ℝ)) = Real.sqrt 2 / 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h3]
      all_goals linarith [Real.sqrt_pos.mpr (show (0: ℝ) < (2: ℝ) by norm_num : (2 : ℝ) > 0)]

    · -- Case where $a^2 - 1 = 0$, so $a^2 = 1$.
      have ha2 : a ^ 2 = 1 := by 
        linarith
      nlinarith [ha.1, ha.2]