import Mathlib

theorem algebra_12504 (a : ℝ) (f : ℝ → ℝ) (hf : f = fun x => Real.sqrt 3 * Real.sin (2 * x) + 2 * (Real.cos x)^2 + a)
    (h : ∀ x ∈ Set.Icc 0 (Real.pi / 2), f x ≥ -1) (ha : ∃ x ∈ Set.Icc 0 (Real.pi / 2), f x = -1) :
    a = -1 := by

  have h1 : ∀ x, f x = Real.sqrt 3 * Real.sin (2 * x) + 2 * (Real.cos x)^2 + a := by
    intro x 
    rw [hf]
    all_goals simp

  have h3 : f (Real.pi / 2) = a := by
    rw [h1]
    have h1 : Real.sin (2 * (Real.pi / 2)) = 0 := by 
      have h1 : 2 * (Real.pi / 2) = Real.pi := by ring
      rw [h1]
      simp [Real.sin_pi]
    have h2 : Real.cos (Real.pi / 2) = 0 := by 
      simp [Real.cos_pi_div_two]
    simp [h1, h2]

  have h5 : a ≥ -1 := by
    have h1' := h (Real.pi / 2) (Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    rw [h3] at h1'
    linarith
  rcases ha with ⟨x₀, hx₀, hfx₀⟩
  have hx₀1 : x₀ ≥ 0 := by 
    have h1 : x₀ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hx₀
    rw [Set.mem_Icc] at h1
    linarith
  have hx₀2 : x₀ ≤ Real.pi / 2 := by 
    have h1 : x₀ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hx₀
    rw [Set.mem_Icc] at h1
    linarith
  have eq1 : f x₀ = Real.sqrt 3 * Real.sin (2 * x₀) + 2 * (Real.cos x₀)^2 + a := h1 x₀
  rw [eq1] at hfx₀
  have h2 : Real.sqrt 3 * Real.sin (2 * x₀) ≥ 0 := by
    have h1 : Real.sin (2 * x₀) ≥ 0 := by
      have h1 : 0 ≤ 2 * x₀ := by linarith
      have h2 : 2 * x₀ ≤ Real.pi := by
        -- because x₀ ≤ Real.pi / 2
        nlinarith [Real.pi_pos, hx₀2]
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      all_goals nlinarith
    have h2 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
    nlinarith [Real.sqrt_nonneg 3, Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ 2 * x₀) (by nlinarith [Real.pi_pos, hx₀2] : 2 * x₀ ≤ Real.pi)]
  -- $0 \leq \sin(2x_0) \leq 1$

  -- $0 \leq \cos^2(x_0) \leq 1$

  have h3 : 2 * (Real.cos x₀)^2 ≥ 0 := by
    nlinarith [sq_nonneg (Real.cos x₀), Real.sin_sq_add_cos_sq x₀]
  -- $0 \leq \cos^2(x_0) \leq 1$

  have h4 : Real.sqrt 3 * Real.sin (2 * x₀) + 2 * (Real.cos x₀)^2 ≥ 0 := by 
    linarith
  -- $a \leq -1$

  have eq3 : a ≤ -1 := by
    nlinarith
  -- $a \geq -1$ and $a \leq -1$, so $a = -1$

  nlinarith