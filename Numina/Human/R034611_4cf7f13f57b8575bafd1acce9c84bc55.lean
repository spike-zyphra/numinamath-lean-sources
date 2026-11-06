import Mathlib
open Real Set
open scoped BigOperators

/- 10. If the function $f(x)=x^{3}-6 x^{2}+9 x$ has a maximum value in $\left(3-a^{2}, a\right)$, then the range of real number $a$ is $\qquad$ -/
theorem calculus_127218 (f : ℝ → ℝ) (hf : f = λ x => x^3 - 6*x^2 + 9*x)
  (a : ℝ) (h : ∃ x ∈ Ioo (3 - a^2) a, f x = 4 ∧ ∀ y ∈ Ioo (3 - a^2) a, f y ≤ 4) :
  a ∈ Ioc (Real.sqrt 2) 4 := by
  -- Compute the derivative, $f'(x) = 3x^2 - 12x + 9 = 3(x-1)(x-3)$.
  have h_deriv : deriv f = λ x => 3 * x^2 - 12 * x + 9 := by
    ext x
    rw [hf]
    rw [deriv_add]
    · rw [deriv_sub]
      · rw [deriv_const_mul, deriv_const_mul]
        · rw [deriv_pow 3, deriv_pow 2, deriv_id'']
          ring
        · exact differentiableAt_id'
        · exact (differentiable_id.pow 2).differentiableAt
      · exact (differentiable_id.pow 3).differentiableAt
      · exact (Differentiable.const_mul (differentiable_id.pow 2) 6).differentiableAt
    · apply DifferentiableAt.sub
      · exact (differentiable_id.pow 3).differentiableAt
      · exact (Differentiable.const_mul (differentiable_id.pow 2) (6 : ℝ)).differentiableAt
    · exact (Differentiable.const_mul differentiable_id (9 : ℝ)).differentiableAt
  have h_deriv_factor : deriv f = λ x => 3 * (x - 1) * (x - 3) := by
    ext x
    rw [h_deriv]
    ring_nf
  -- Compute $f(1)$, $f(4)$ to confirm maximum values.
  have h_f1 : f 1 = 4 := by
    rw [hf]
    simp
    ring
  have h_f4 : f 4 = 4 := by
    rw [hf]
    simp
    ring
  -- From condition h, there exists $x ∈ (3 - a^2, a)$ such that $f(x) = 4$.
  have h_max : ∃ x ∈ Ioo (3 - a^2) a, f x = 4 := by
    obtain ⟨x, hx, hfx, _⟩ := h
    exact ⟨x, hx, hfx⟩
  -- Points where $f(x) = 4$.
  have h_f_eq_4 : {x | f x = 4} = {1, 4} := by
    ext x
    rw [hf]
    simp
    have : x^3 - 6 * x^2 + 9 * x - 4 = (x - 1)^2 * (x - 4) := by
      calc
        x^3 - 6 * x^2 + 9 * x - 4 = (x - 1) * (x^2 - 5 * x + 4) := by ring
        _ = (x - 1) * (x - 1) * (x - 4) := by
          have factor_x2_minus_5x_plus_4 : x^2 - 5 * x + 4 = (x - 1) * (x - 4) := by ring
          rw [factor_x2_minus_5x_plus_4,← mul_assoc]
        _ = (x - 1)^2 * (x - 4) := by ring
    apply Iff.intro
    · intro h
      have h': x^3 - 6 * x^2 + 9 * x - 4 = 0 := by linarith [h]
      rw [this] at h'
      have : (x - 1)^2 * (x - 4) = 0 → x = 1 ∨ x = 4 := by
        intro h''
        apply Or.elim (mul_eq_zero.mp h'')
        · intro h1
          have : (x - 1)^2 = 0 := by exact h1
          have : x - 1 = 0 := by exact pow_eq_zero this
          left
          linarith
        · intro h2
          right
          linarith
      exact this h'
    · intro h
      simp at h
      cases h with
      | inl h1 =>
        rw [h1]
        norm_num
      | inr h2 =>
        rw [h2]
        norm_num
  -- $x = 1$ or $x = 4$ lies within the interval $(3 - a^2, a)$.
  have h_x_in : ∃ x ∈ ({1, 4} : Set ℝ), x ∈ Ioo (3 - a^2) a := by
    obtain ⟨x, hx, hfx⟩ := h_max
    have : x ∈ {x | f x = 4} := by simp [hfx]
    rw [h_f_eq_4] at this
    exact ⟨x, this, hx⟩
  -- Interval condition $3 - a^2 < 1 < a$.
  have h_interval : 3 - a^2 < 1 ∧ 1 < a := by
    rcases h_x_in with ⟨x, hx_set, hx_interval⟩
    simp at hx_set
    cases hx_set with
    | inl h1 =>
      rw [h1] at hx_interval
      exact ⟨hx_interval.1, hx_interval.2⟩
    | inr h2 =>
      rw [h2] at hx_interval
      have : 3 - a^2 < 4 := by linarith [hx_interval.1]
      have : 4 < a := by linarith [hx_interval.2]
      exact ⟨by nlinarith, by nlinarith⟩
  -- Solve the inequality $3 - a^2 < 1$.
  have h_a_lower : Real.sqrt 2 < a := by
    have s1: a^2 > 2 := by linarith
    have s2 : 0 ≤ a := by linarith [h_interval.2]
    have s3: √(a^2) > √2 := by gcongr
    rw [Real.sqrt_sq s2] at s3
    exact s3
  -- From $f(x) = 4$ and interval conditions, deduce $a ≤ 4$.
  have h_a_upper : a ≤ 4 := by
    by_contra h_contra
    push_neg at h_contra
    -- Prove that $f$ is strictly increasing on $[4, ∞)$.
    have h_mono : ∀ x y, 4 ≤ x → x < y → f x < f y := by
      intros x y h_x h_xy
      have h_deriv_pos : ∀ z, 4 ≤ z → 0 < deriv f z := by
        intros z h_z
        rw [h_deriv_factor]
        have : z - 1 > 0 := by linarith [h_z]
        have : z - 3 > 0 := by linarith [h_z]
        simp [this, this]
        linarith
      have h_mono_on : StrictMonoOn f (Icc 4 (max x y)) := by
        apply strictMonoOn_of_deriv_pos
        · apply convex_Icc
        · rw [hf]
          apply ContinuousOn.add
          · apply ContinuousOn.sub
            · apply continuous_pow 3 |>.continuousOn
            · apply (continuous_const.mul (continuous_pow 2)).continuousOn
          · apply (continuous_const.mul continuous_id').continuousOn
        · intros z h_z
          have h_z_Icc : z ∈ Icc 4 (max x y) := interior_subset h_z
          apply h_deriv_pos
          exact (Set.mem_Icc.mp h_z_Icc).1
      apply h_mono_on
      · simp [h_x]
      · have h_y_ge_4 : 4 ≤ y := le_trans h_x (le_of_lt h_xy)
        simp [h_y_ge_4]
      · exact h_xy
    -- Assume $a > 4$, the interval $(3 - a^2, a)$ contains $x > 4$.
    have h_x_large : ∃ x' ∈ Ioo (3 - a^2) a, 4 < x' := by
      exists (4 + a) / 2
      constructor
      · constructor
        · linarith [h_interval.1]
        · linarith [h_contra]
      · linarith
    obtain ⟨x', hx'_interval, hx'_large⟩ := h_x_large
    have : f x' > f 4 := by
      apply h_mono
      · linarith
      · exact hx'_large
    have : f 4 = 4 := h_f4
    rw [this] at this
    -- Contradiction: h_max_val requires $f y ≤ 4$.
    obtain ⟨x, hx, hfx, h_max_val⟩ := h
    have : f x' ≤ 4 := h_max_val x' hx'_interval
    linarith [this, this]
  -- Combine the lower and upper bounds.
  have h_a : Real.sqrt 2 < a ∧ a ≤ 4 := ⟨h_a_lower, h_a_upper⟩
  exact h_a
