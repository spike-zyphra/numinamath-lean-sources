import Mathlib

/- Let $f$ be a second-degree polynomial such that the equation $f(x)=x$ has no real solution. Show that the equation $f(f(x))=x$ has no real solution. -/
theorem algebra_142304 {f : Polynomial ℝ} (hf : f.degree = 2) (hfn : ∀ x : ℝ, f.eval x ≠ x) :
    ∀ x : ℝ, f.eval (f.eval x) ≠ x := by
  -- Define g(x) = f(x) - x
  let g := f - Polynomial.X

  -- Since g(x) = f(x) - x, we have g(x) = 0 iff f(x) = x
  -- By assumption, f(x) ≠ x for all x, so g(x) ≠ 0 for all x
  have hg : ∀ x : ℝ, g.eval x ≠ 0 := by
    intro x
    -- g(x) = f(x) - x, so g(x) = 0 iff f(x) = x
    have : g.eval x = f.eval x - x := by
      simp [g, Polynomial.eval_sub, Polynomial.eval_X]
    rw [this]
    -- Now we need to prove f.eval x - x ≠ 0
    -- This is equivalent to f.eval x ≠ x, which is our assumption
    rw [sub_ne_zero]
    exact hfn x

  -- For a degree 2 polynomial with no roots, it has a constant sign
  -- depending on the sign of the leading coefficient
  have h_sign : (∀ x : ℝ, g.eval x > 0) ∨ (∀ x : ℝ, g.eval x < 0) := by
    -- Using proof by contradiction: assume g is neither always positive nor always negative
    by_contra h
    push_neg at h

    -- Obtain x₁ and x₂ such that g(x₁) > 0 and g(x₂) < 0
    -- The negation of h is ¬((∀ x, g.eval x > 0) ∨ (∀ x, g.eval x < 0))
    -- This is equivalent to (∃ x, g.eval x ≤ 0) ∧ (∃ x, g.eval x ≥ 0)
    -- Adding the condition g.eval x ≠ 0, we get (∃ x, g.eval x < 0) ∧ (∃ x, g.eval x > 0)
    obtain ⟨⟨x₁, h₁⟩, ⟨x₂, h₂⟩⟩ := h

    -- Based on the above analysis, use h₁ and h₂ to find one positive and one negative point
    have h₁_not_pos : g.eval x₁ ≤ 0 := h₁
    have h₂_not_neg : g.eval x₂ ≥ 0 := h₂

    -- Combining with the condition g.eval x ≠ 0 to get strict inequality
    have h₁_neg : g.eval x₁ < 0 := by
      have : g.eval x₁ ≠ 0 := hg x₁
      exact lt_of_le_of_ne h₁_not_pos this

    have h₂_pos : g.eval x₂ > 0 := by
      have : g.eval x₂ ≠ 0 := hg x₂
      exact lt_of_le_of_ne' h₂_not_neg this

    -- Polynomial is a continuous function
    have g_cont : Continuous (fun x => g.eval x) := Polynomial.continuous g

    -- Apply the intermediate value theorem: if a continuous function takes positive and negative values at two points,
    -- then there must be a zero point between these two points
    have zero_exists : ∃ z, g.eval z = 0 := by
      -- First determine the order of points
      by_cases h_order : x₂ ≤ x₁
      · -- Case: x₂ ≤ x₁
        -- Convert global continuity to continuity on the interval
        have g_cont_on : ContinuousOn (fun x => g.eval x) (Set.Icc x₂ x₁) :=
          g_cont.continuousOn

        -- 0 is between g(x₂) and g(x₁)
        have h_zero_in_range : 0 ∈ Set.Icc (g.eval x₁) (g.eval x₂) := by
          simp only [Set.mem_Icc]
          constructor
          · exact le_of_lt h₁_neg  -- g(x₁) < 0 so g(x₁) ≤ 0
          · exact le_of_lt h₂_pos  -- 0 < g(x₂) so 0 ≤ g(x₂)

        -- Use Intermediate Value Theorem
        have h_zero_exists := intermediate_value_Icc' h_order g_cont_on

        -- Apply to our case
        have zero_in_range := h_zero_exists h_zero_in_range

        -- Extract the zero point
        have ⟨z, z_in_Icc, hz⟩ : ∃ z, z ∈ Set.Icc x₂ x₁ ∧ g.eval z = 0 := by
          rw [← Set.mem_image]
          exact zero_in_range
        exact ⟨z, hz⟩

      · -- Case: x₁ < x₂
        push_neg at h_order
        have h_le : x₁ ≤ x₂ := le_of_lt h_order

        -- Apply the same intermediate value theorem
        have g_cont_on : ContinuousOn (fun x => g.eval x) (Set.Icc x₁ x₂) :=
          g_cont.continuousOn

        -- 0 is between g(x₁) and g(x₂)
        have h_zero_in_range : 0 ∈ Set.Icc (g.eval x₁) (g.eval x₂) := by
          simp only [Set.mem_Icc]
          constructor
          · exact le_of_lt h₁_neg
          · exact le_of_lt h₂_pos

        -- Use Intermediate Value Theorem
        have h_zero_exists := intermediate_value_Icc h_le g_cont_on

        -- Apply to our case
        have zero_in_range := h_zero_exists h_zero_in_range

        -- Extract the zero point
        have ⟨z, z_in_Icc, hz⟩ : ∃ z, z ∈ Set.Icc x₁ x₂ ∧ g.eval z = 0 := by
          rw [← Set.mem_image]
          exact zero_in_range
        exact ⟨z, hz⟩

    -- Extract the zero point
    obtain ⟨z, hz⟩ := zero_exists

    -- This contradicts hg, which states that g is non-zero at all points
    exact hg z hz

  intro x

  -- If g(y) > 0 for all y, then f(y) > y for all y
  -- If g(y) < 0 for all y, then f(y) < y for all y
  -- In either case, we can prove that f(f(x)) ≠ x

  cases h_sign with
  | inl h_pos => -- Case: f(y) > y for all y
    -- This means f(x) > x
    have h_fx_gt_x : f.eval x > x := by
      -- Since g(x) = f(x) - x, we have f(x) = g(x) + x
      have hfgx : f.eval x = g.eval x + x := by
        simp [g, Polynomial.eval_sub, Polynomial.eval_X]

      -- Use this equality to compare f(x) and x
      rw [hfgx]

      -- We're in the h_pos case, which means g(x) > 0 for all x
      have hgx_pos : g.eval x > 0 := h_pos x

      -- Therefore, f(x) = g(x) + x > 0 + x = x
      exact lt_add_of_pos_left x hgx_pos

    -- And f(f(x)) > f(x)
    have h_ffx_gt_fx : f.eval (f.eval x) > f.eval x := by
      -- For any y, we know g(y) > 0, which means f(y) > y
      -- Let's substitute y = f.eval x
      -- We need to show f(f(x)) > f(x), which is exactly f(y) > y when y = f(x)

      -- First, we need to establish that f(y) > y for all y from g(y) > 0
      have h_f_gt_y : ∀ y : ℝ, f.eval y > y := by
        intro y
        -- Since g(y) = f(y) - y, we have f(y) = g(y) + y
        have : f.eval y = g.eval y + y := by
          simp [g, Polynomial.eval_sub, Polynomial.eval_X]
        rw [this]
        -- Since g(y) > 0, we have g(y) + y > y
        exact lt_add_of_pos_left y (h_pos y)

      -- Now apply this to y = f.eval x
      exact h_f_gt_y (f.eval x)

    -- By transitivity, f(f(x)) > x
    have h_ffx_gt_x : f.eval (f.eval x) > x := by
      apply lt_trans h_fx_gt_x h_ffx_gt_fx

    -- Therefore, f(f(x)) ≠ x
    exact ne_of_gt h_ffx_gt_x

  | inr h_neg => -- Case: f(y) < y for all y
    -- This means f(x) < x
    have h_fx_lt_x : f.eval x < x := by
      -- Since g(x) = f(x) - x, we have f(x) = g(x) + x
      have hfgx : f.eval x = g.eval x + x := by
        simp [g, Polynomial.eval_sub, Polynomial.eval_X]

      -- Use this equality to compare f(x) and x
      rw [hfgx]

      -- We're in the h_neg case, which means g(x) < 0 for all x
      have hgx_neg : g.eval x < 0 := h_neg x

      -- Therefore, f(x) = g(x) + x < 0 + x = x
      exact add_lt_of_neg_of_le hgx_neg (le_refl x)

    -- And f(f(x)) < f(x)
    have h_ffx_lt_fx : f.eval (f.eval x) < f.eval x := by
      -- For any y, we know g(y) < 0, which means f(y) < y
      -- Let's substitute y = f.eval x
      -- We need to show f(f(x)) < f(x), which is exactly f(y) < y when y = f(x)

      -- First, we need to establish that f(y) < y for all y from g(y) < 0
      have h_f_lt_y : ∀ y : ℝ, f.eval y < y := by
        intro y
        -- Since g(y) = f(y) - y, we have f(y) = g(y) + y
        have : f.eval y = g.eval y + y := by
          simp [g, Polynomial.eval_sub, Polynomial.eval_X]
        rw [this]
        -- Since g(y) < 0, we have g(y) + y < y
        exact add_lt_of_neg_of_le (h_neg y) (le_refl y)

      -- Now apply this to y = f.eval x
      exact h_f_lt_y (f.eval x)

    -- By transitivity, f(f(x)) < x
    have h_ffx_lt_x : f.eval (f.eval x) < x := by
      apply lt_trans h_ffx_lt_fx h_fx_lt_x

    -- Therefore, f(f(x)) ≠ x
    exact ne_of_lt h_ffx_lt_x
