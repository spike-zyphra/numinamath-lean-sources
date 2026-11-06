import Mathlib


/- Let $x$ be a real number such that $$x^2 + 4 \left( \frac{x}{x - 2} \right)^2 = 45.$$Find all possible values of $y = \frac{(x - 2)^2 (x + 3)}{2x - 3}.$  Enter all possible values, separated by commas. -/
theorem algebra_11161
    (f : ℝ → ℝ)
    (hf : f = fun t => ((t - 2) ^ 2 * (t + 3)) / (2 * t - 3)) :
    {y | ∃ x, x ^ 2 + 4 * (x / (x - 2)) ^ 2 = 45 ∧ y = f x} = {2, 16} := by

  ext y

  constructor
  . intro h
    dsimp at h
    obtain ⟨x, ⟨h, hy⟩⟩ := h
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, hy]
    -- From the given equation, $x^2 + \left( \frac{2x}{x - 2} \right)^2 - 45 = 0.$
    apply sub_eq_zero_of_eq at h

    -- aux prop, x - 2 ≠ 0, 2 * x - 3 ≠ 0
    have h_xmtwone0 : x - 2 ≠ 0 := by
      by_contra! h_contra
      have : x = 2 := by linarith only [h_contra]
      rw [this] at h
      norm_num at h
    have h_2mxm3ne0 : 2 * x - 3 ≠ 0 := by
      by_contra! h_contra
      have : x = 3 / 2 := by linarith only [h_contra]
      rw [this] at h
      norm_num at h

    -- Let $a = x$ and $b = \frac{2x}{x - 2}.$ Then $a^2 + b^2 = 45,$ or $(a + b)^2 - 2ab - 45 = 0.$
    -- We can write this as $\left( \frac{x^2}{x - 2} \right)^2 - \frac{4x^2}{x - 2} - 45 = 0.$
    have : (x ^ 2 / (x - 2)) ^ 2 - (4 * x ^ 2) / (x - 2) - 45 = 0 := by
      let a := x
      let b := (2 * x) / (x - 2)
      have : a ^ 2 + b ^ 2 - 45 = 0 := by
        convert h
        dsimp [a, b]
        field_simp
        ring_nf
      have t0 : (a + b) ^ 2 - 2 * a * b - 45 = 0 := by
        rw [add_sq, add_sub_assoc, add_assoc, add_sub_cancel]
        exact this
      have t1 : a + b = x ^ 2 / (x - 2) := by
        dsimp [a, b]
        calc
          _ = x * (x - 2) / (x - 2) + 2 * x / (x - 2) := by
            rw [mul_div_cancel_right₀ _ h_xmtwone0]
          _ = x ^ 2 / (x - 2) := by
            rw [← add_div, mul_sub, mul_comm x 2, sub_add_cancel, ← pow_two]
      convert t0 using 3
      . rw [t1]
      . dsimp [a, b]
        field_simp
        ring_nf

    -- Let $y = \frac{x^2}{x - 2}.$  Then $y^2 - 4y - 45 = 0,$ which factors as $(y - 9)(y + 5) = 0.$ So, $$\left( \frac{x^2}{x - 2} - 9 \right) \left( \frac{x^2}{x - 2} + 5 \right) = 0.$$
    have : (x ^ 2 / (x - 2) - 9) * (x ^ 2 / (x - 2) + 5) = 0 := by
      rw [mul_div_assoc] at this
      ring_nf at this
      ring_nf
      linarith only [this]

    -- Then $(x^2 - 9x + 18)(x^2 + 5x - 10) = 0,$ which factors as $$(x - 3)(x - 6)(x^2 + 5x - 10) = 0.$$
    have : (x - 3) * (x - 6) * (x ^ 2 + 5 * x - 10) = 0 := by
      apply_fun fun t => (x - 2) * t * (x - 2) at this
      rw [← mul_assoc, mul_sub (x - 2), mul_div_cancel₀ _ h_xmtwone0, mul_assoc, add_mul, div_mul_cancel₀ _ h_xmtwone0, mul_zero, zero_mul] at this
      ring_nf at this
      ring_nf
      linarith only [this]

    have : x - 3 = 0 ∨ x - 6 = 0 ∨ x ^ 2 + 5 * x - 10 = 0 := by aesop

    rcases this with hx | hx | hx

    -- If $x = 3,$ then $\frac{(x - 2)^2 (x + 3)}{2x - 3} = 2.$
    . left
      have hxv : x = 3 := by linarith
      simp only [hf, hxv]
      norm_num

    -- If $x = 6,$ then $\frac{(x - 2)^2 (x + 3)}{2x - 3} = 16.$
    . right
      have hxv : x = 6 := by linarith
      simp only [hf, hxv]
      norm_num

    -- If $x^2 + 5x - 10 = 0,$
    . right
      -- then $x^2 = -5x + 10,$
      have r1 : x ^ 2 = -5 * x + 10 := by
        linarith

      -- and $x^3 = x(-5x + 10) = -5x^2 + 10x = -5(-5x + 10) + 10x = 35x - 50.$
      have r2 : x ^ 3 = 35 * x - 50 := by
        calc x ^ 3
          _ = x * (-5 * x + 10) := by
            rw [pow_succ', r1]
          _ = -5 * x ^ 2 + 10 * x := by
            linarith only
          _ = -5 * (-5 * x + 10) + 10 * x := by
            rw [r1]
          _ = 35 * x - 50 := by
            linarith only

      -- Hense $$ \begin{aligned} \frac{x^3 - x^2 - 8x + 12}{2x - 3} &= \frac{(35x - 50) - (-5x + 10) - 8x + 12}{2x - 3} \\ &= \frac{32x - 48}{2x - 3} = 16. \end{aligned} $$
      simp only [hf]
      calc
        _ = (x ^ 3 - x ^ 2 - 8 * x + 12) / (2 * x - 3) := by
          ring_nf
        _ = ((35 * x - 50) - (-5 * x + 10) - 8 * x + 12) / (2 * x - 3) := by
          rw [r1, r2]
        _ = (32 * x - 48) / (2 * x - 3) := by
          ring_nf
        _ = 16 := by
          rw [show 32 * x - 48 = 16 * (2 * x - 3) by linarith only, mul_div_cancel_right₀ _ h_2mxm3ne0]

  -- varify the values are valid
  . intro h
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    simp only [Set.mem_setOf_eq, hf]
    rcases h with h | h
    . use 3
      norm_num [h]
    . use 6
      norm_num [h]
