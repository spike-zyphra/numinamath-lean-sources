import Mathlib

theorem algebra_194619 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + a * x + b)
    (h0 : f (f 0) = 0) (h1 : f (f 1) = 0) (h2 : f 0 ≠ f 1) :
    f 2 = 3 := by

  have h3 : f 0 = b := by
    rw [hf]
    all_goals norm_num

  have h4 : f 1 = 1 + a + b := by
    rw [hf]
    all_goals ring

  have h5 : f (f 0) = b ^ 2 + a * b + b := by
    rw [h3]
    rw [hf]
    all_goals ring

  -- Substituting in h0 gives us the equation b ^ 2 + a * b + b = 0
  rw [h5] at h0

  -- Compute f(f(1)) by first computing f(1)
  -- Then compute f(f(1)) = f(1 + a + b)
  have h6 : f (f 1) = (1 + a + b) ^ 2 + a * (1 + a + b) + b := by
    rw [h4]
    rw [hf]
    all_goals ring

  -- Substituting in h1 gives us the equation (1 + a + b)^2 + a * (1 + a + b) + b = 0
  rw [h6] at h1

  -- From h2: f(0) ≠ f(1), which means b ≠ 1 + a + b
  have h7 : b ≠ 1 + a + b := by
    by_contra h
    have : f 0 = f 1 := by
      rw [h3, h4]
      linarith
    contradiction

  have h8 : a ≠ -1 := by
    by_contra h9
    have h11 : b = 1 + a + b := by
      linarith [h9]
    have h7' : b ≠ 1 + a + b := h7
    contradiction

  -- From h0: $b^2 + a * b + b = 0$ can be written as $b(a + b + 1) = 0$
  have h9 : b * (a + b + 1) = 0 := by
    nlinarith

  cases' (mul_eq_zero.1 h9) with hb1 ha1
  · -- Case where b = 0
    have hb0 : b = 0 := hb1
    have h12 : (1 + a + b) ^ 2 + a * (1 + a + b) + b = 0 := by nlinarith
    rw [hb0] at h12
    -- Equation simplified to $(1 + a)^2 + a(1 + a) = 0$
    have h13 : (1 + a) ^ 2 + a * (1 + a) = 0 := by
      nlinarith
    have h14 : a = -1 / 2 := by
      have h15 : a + 1 ≠ 0 := by
        intro h
        apply h8
        linarith
      apply (mul_left_inj' (show a + 1 ≠ 0 by assumption)).mp
      linarith [h13]
      all_goals nlinarith [sq_pos_of_ne_zero (show a + 1 ≠ 0 by assumption)]
    have h15 : f 2 = 3 := by
      rw [hf]
      rw [h14, hb0]
      norm_num
    exact h15

  · -- Case where a + b + 1 = 0
    have ha2 : a + b + 1 = 0 := by linarith [ha1]
    have hb2 : b = -a - 1 := by linarith
    rw [hb2] at h1
    have h14 : a = -1 := by
      nlinarith
    contradiction