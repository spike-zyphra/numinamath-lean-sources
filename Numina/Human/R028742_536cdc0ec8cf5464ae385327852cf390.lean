import Mathlib

/- Find all functions $f$ from the set $\mathbf{R}$ of real numbers into $\mathbf{R}$ which satisfy for all $x, y, z \in \mathbf{R}$ the identity

$$
f(f(x)+f(y)+f(z))=f(f(x)-f(y))+f(2 x y+f(z))+2 f(x z-y z) .
$$ -/

theorem algebra_260846 (f : ℝ → ℝ) :
    (∀ x y z, f (f x + f y + f z) = f (f x - f y) + f (2 * x * y + f z) +
      2 * f (x * z - y * z)) ↔ (∀ x, f x = 0) ∨ (∀ x, f x = x ^ 2) := by
  constructor
  · -- Forward direction
    intro h_func_eq

    -- Check if f is the zero function
    by_cases h_zero : ∀ x, f x = 0
    · -- If f is identically zero, we're done
      left
      exact h_zero
    · -- If f is not identically zero
      right

      -- f is not constant
      have h_nonconst : ¬ (∃ c, ∀ x, f x = c) := by
        have h0 := h_func_eq 0 0 0
        simp at h0
        by_contra h
        obtain ⟨c, hc⟩ := h
        have h1 := hc (f 0+f 0+f 0)
        have h2 := hc (0)
        have h3 := hc (c)
        rw [h1, h2, h3] at h0
        have : c=0 := by
          linarith
        rw [this] at hc
        exact h_zero hc

      -- Let t ∈ ℝ and substitute (x,y,z)=(t,0,0) and (x,y,z)=(0,t,0)
      have h_t00 : ∀ t, f (f t + f 0 * 2) = f 0 * 2 + f (f t - f 0) + f (f 0):= by
        intro t
        have := h_func_eq t 0 0
        ring_nf at this
        exact this

      have h_0t0 : ∀ t, f (f t + f 0 * 2) = f 0 * 2 + f (f 0 - f t) + f (f 0) := by
        intro t
        have := h_func_eq 0 t 0
        ring_nf at this
        rw [add_comm]
        exact this

      -- From these we get f(f(t) - f(0)) = f(f(0) - f(t))
      have h_symm : ∀ t, f (f 0 - f t) = f (-f 0 + f t) := by
        intro t
        have h1 := h_t00 t
        have h2 := h_0t0 t
        rw [h2] at h1
        ring_nf at h1
        linarith

      -- f(u1)=f(u2) then f(su1)=f(su2)
      have h_f_eq : ∀ u1 u2, f u1 = f u2 → ∀ s, f (s * u1) = f (s * u2) := by
        intro u1 u2 h_eq s
        have h1 := h_func_eq s 0 u1
        have h2 := h_func_eq s 0 u2
        rw [h_eq] at h1
        rw [h1] at h2
        ring_nf at h2
        linarith

      -- Since f is not constant, there exists s₀ such that f(s₀) ≠ f(0)
      have h_s_nonconst : ∃ s₀, f s₀ ≠ f 0 := by
        by_contra h
        push_neg at h

        have : ∃ c, ∀ x, f x = c := by
          use f 0

        exact h_nonconst this

      -- Let u₁ = f(s₀) - f(0), u₂ = -u₁
      obtain ⟨s₀, h_s₀⟩ := h_s_nonconst
      let u₁ := f s₀ - f 0
      let u₂ := -u₁
      have h_u₁ : u₁ = f s₀ - f 0 := rfl
      have h_u₂ : u₂ = -u₁ := rfl
      have h_u1_ne_0 : u₁ ≠ 0 := by
        rw [h_u₁]
        by_contra h
        rw [sub_eq_zero] at h
        exact h_s₀ h

      -- Then f(u₁) = f(u₂)
      have h_u : f u₁ = f u₂ := by
        have := h_symm s₀
        rw [←sub_eq_neg_add] at this
        rw [h_u₂, h_u₁, neg_sub]
        exact this.symm

      -- For any s, f(su₁) = f(su₂) = f(-su₁)
      have h_su : ∀ s, f (s * u₁) = f (-(s * u₁)) := by
        intro s
        -- use h_f_eq and h_u to show f(s*u1)=f(s*u2)
        apply h_f_eq at h_u
        rw [h_u,h_u₂]
        rw [mul_neg]

      -- Step 1: Prove f is an even function: f(-x) = f(x)
      -- Since u₁ ≠ 0, we conclude f(x) = f(-x) for all x
      have f_even : ∀ x, f (-x) = f x := by
        intro x
        have := h_su (x/u₁)
        field_simp at this
        exact this.symm

      have h_s_ne_0 : ∀ s, s ≠ 0 → f s ≠ f 0 := by
        intro s h_ne_0
        by_contra h
        have := h_f_eq s 0 h
        simp at this
        have h_is_const : ∃ c, ∀ (x : ℝ), f x = c := by
          use f 0
          intro x
          have h := this (x/s)
          field_simp at h
          exact h
        exact h_nonconst h_is_const

      -- Step 2: Prove if f(x) = f(y), then x = y or x = -y
      have f_inj_or_neg : ∀ {x y}, f x = f y → x = y ∨ x = -y := by
        intro x y h_eq
        -- Assume it's not the case that x = y or x = -y
        by_cases hx0 : x = 0
        · -- If x = y or x = -y, we're done
          by_cases h_cases_1 : y = 0
          · -- If y = 0, then x = 0
            left
            linarith
          · -- If y ≠ 0
            rw [hx0] at h_eq
            have := ((h_s_ne_0 y) h_cases_1).symm
            contradiction

        · -- If not, we'll derive a contradiction by showing f must be constant
          push_neg at hx0
          -- So we have x ≠ y and x ≠ -y
          by_cases hy0 : y = 0
          · -- If y = 0, then x ≠ 0
            rw [hy0] at h_eq
            have := (h_s_ne_0 x) hx0
            contradiction
          · -- If y ≠ 0
            -- There exists r > 0, r ≠ 1 such that f(x) = f(r*x) for all x
            -- We follow the proof outline where r = y/x (or a similar ratio)
            -- The key insight is: if f(x₀)=f(y₀) with x₀≠y₀ and x₀≠-y₀,
            -- we can define a ratio r and show f(z)=f(r*z) for all z

            by_cases hxy : x=y ∨ x=-y
            · -- If x = y, we're done
              exact hxy
            · -- If x ≠ y, we need to find a ratio r
              push_neg at hxy

              -- Derive that for all x, f(x)=f(rx)
              have h_r_scale : ∃ r, r > 0 ∧ r ≠ 1 ∧ ∀ z, f z = f (r * z) := by
                -- 对 x 和 y 的符号分情况讨论
                by_cases h_sign : (x > 0 ∧ y > 0) ∨ (x < 0 ∧ y < 0)
                ·
                  use y / x
                  constructor
                  · -- y/x > 0
                    cases h_sign with
                    | inl h_left =>
                      obtain ⟨h1,h2⟩ := h_left
                      exact div_pos h2 h1
                    | inr h_right =>
                      obtain ⟨h1,h2⟩ := h_right
                      exact div_pos_of_neg_of_neg h2 h1

                  constructor
                  · -- y/x ≠ 1
                    field_simp
                    exact hxy.1.symm

                  · -- ∀ z, f z = f (r * z)
                    intro z
                    have := ((h_f_eq x y) h_eq) (z/x)
                    field_simp at this
                    rw [mul_comm,←mul_div_assoc]
                    exact this
                ·
                  push_neg at h_sign

                  -- (x > 0 ∧ y < 0) ∨ (x < 0 ∧ y > 0)
                  have h_opp_sign : (x > 0 ∧ y < 0) ∨ (x < 0 ∧ y > 0) := by
                    by_cases h_x_pos : x > 0
                    ·
                      left
                      exact ⟨h_x_pos, lt_of_le_of_ne (h_sign.1 h_x_pos) hy0⟩
                    ·
                      right
                      have h_x_le_0 : x<0 := by
                        simp at h_x_pos
                        exact lt_of_le_of_ne h_x_pos hx0
                      exact ⟨h_x_le_0, lt_of_le_of_ne (h_sign.2 h_x_le_0) (Ne.symm hy0)⟩

                  use -y / x
                  constructor
                  · -- -y/x > 0
                    cases h_opp_sign with
                    | inl h_left =>
                      obtain ⟨h1,h2⟩ := h_left
                      have : -y>0 := by linarith
                      exact div_pos this h1
                    | inr h_right =>
                      obtain ⟨h1,h2⟩ := h_right
                      have : -y<0 := by linarith
                      exact div_pos_of_neg_of_neg this h1

                  constructor
                  · -- -y/x ≠ 1
                    field_simp
                    exact hxy.2.symm

                  · -- ∀ z, f z = f (r * z)
                    intro z
                    have h1:= ((h_f_eq x y) h_eq) (z/x)
                    field_simp at h1
                    have : -y / x * z=-(z * y / x) := by ring
                    rw [h1, this]
                    exact (f_even (z*y/x)).symm

              -- Extract the ratio r from the proof above
              obtain ⟨r, h_r_pos, h_r_ne_1, h_scale⟩ := h_r_scale

              have h_scale2: ∀ z, f (r^2 * z) = f (z) := by
                intro z
                have h1 : r^2 * z = r * (r * z) := by ring
                rw [h1,←h_scale,←h_scale]

              -- Substitute values into the functional equation and compare
              have h_rz : ∀ x y z, f (r * x * z - r * y * z) = f (r ^ 2 * x * z - y * z) := by
                intro x y z
                have h1:= h_func_eq (r*x) (r*y) z
                have h2:= h_func_eq (r^2*x) y z
                rw [←h_scale,←h_scale] at h1

                have h3: 2 * (r * x) * (r * y) + f z = 2 * (r ^ 2 * x) * y + f z := by ring
                rw [h_scale2,h1,h3] at h2
                simp at h2
                exact h2

              -- For arbitrary u, v, we can find appropriate values to substitute
              have h_uv : ∀ u v, f u = f v := by
                intro u v
                have h := h_rz ((v-u)/((r^2)-1)) ((v-(r^2)*u)/((r^2)-1)) 1
                field_simp at h
                have : r^2-1 ≠ 0 := by
                  by_contra h_neg
                  have h_factor : r^2 - 1 = (r+1)*(r-1) := by ring
                  rw [h_factor] at h_neg
                  have h_cases : r+1=0 ∨ r-1=0 := by exact mul_eq_zero.mp h_neg

                  cases h_cases with
                  | inl h_left =>
                    have : r = -1 := by linarith
                    have h_neg : -1 < 0 := by norm_num
                    linarith
                  | inr h_right =>
                    have : r = 1 := by linarith
                    exact h_r_ne_1 this

                have h1 : r * (v - u) / (r ^ 2 - 1) - r * (v - r ^ 2 * u) / (r ^ 2 - 1) = r * u := by
                  field_simp
                  ring

                have h2: r ^ 2 * (v - u) / (r ^ 2 - 1) - (v - r ^ 2 * u) / (r ^ 2 - 1) = v := by
                  field_simp
                  ring

                rw [h1,h2] at h
                rw [←h]
                exact h_scale u

              -- This implies f is constant, contradicting our assumption
              have h_const : ∃ c, ∀ x, f x = c := by
                use f 0
                intro x
                have h := h_uv x 0
                rw [h]

              -- Contradiction with f being non-constant
              have contra : False := h_nonconst h_const
              contradiction

      -- Step 3: Prove f(0) = 0
      have f0 : f 0 = 0 := by
        have h_neg : ∀ x y, f (2 * x * y + f 0) = f (-(2 * x * y) + f 0) := by
          intro x y
          have h_z0a : f (f x + f y + f 0) = f (f x - f y) + f (2 * x * y + f 0) + 2 * f 0 := by
            -- Substitute z = 0 in the functional equation
            have := h_func_eq x y 0
            simp at this
            exact this
          have h_z0b : f (f x + f y + f 0) = f (f x - f y) + f (- (2 * x * y) + f 0) + 2 * f 0 := by
            have := h_func_eq x (-y) 0
            simp at this
            have h : f (-y) = f y := by
              exact (f_even y)
            rw [h] at this
            exact this

          rw [h_z0a] at h_z0b
          simp at h_z0b
          exact h_z0b

        -- Choose x=1, y=1 to get f(2 + f(0)) = f(-2 + f(0))
        -- By f_inj_or_neg, either 2 + f(0) = -2 + f(0) or 2 + f(0) = -((-2) + f(0))
        -- First case: 2 + f(0) = -2 + f(0) implies 4 = 0, which is impossible
        -- Second case: 2 + f(0) = 2 - f(0) implies f(0) = 0
        have := h_neg 1 1
        simp at this
        apply f_inj_or_neg at this
        -- this : 2 + f 0 = -2 + f 0 ∨ 2 + f 0 = -(-2 + f 0)

        cases this with
        | inl h_case1 => -- First case: 2 + f 0 = -2 + f 0
          have : 2 + 2 = 0 := by linarith
          contradiction

        | inr h_case2 => -- Second case: 2 + f 0 = -(-2 + f 0)
          -- Simplify right side: -(-2 + f 0) = 2 - f 0
          simp at h_case2
          linarith

      -- Step 4: Prove f(x) = x^2
      have f_square : ∀ x, f x = x^2 := by
        intro x

        -- Let x = y in the functional equation
        have h_xx : ∀ x' z,  f x' = x' ^ 2 ∨ 2 * f x' + f z = -f z + -(2 * x' ^ 2) := by
          intro x' z
          have h1 := h_func_eq x' x' z
          simp at h1
          rw [f0] at h1
          simp at h1
          have h2: f x' + f x' + f z = 2 * f x' + f z := by ring
          have h3 : 2*x'*x'=2*x'^2 := by ring
          rw [h2,h3] at h1
          apply f_inj_or_neg at h1
          simp at h1
          exact h1

        by_contra h_neg

        have h_const : ∃ c, ∀ z, f z = c := by
          use - f x- x^2
          intro z
          apply Or.elim (h_xx x z)
          . intro h_left
            contradiction
          . intro h_right
            linarith

        exact h_nonconst h_const

      -- Conclude that f(x) = x^2 for all x
      exact f_square

  · -- Backward direction
    intro h
    cases h with
    | inl h_zero => -- Case: f(x) = 0 for all x
      intro x y z
      -- Apply h_zero to all terms
      repeat rw [h_zero]
      simp

    | inr h_square => -- Case: f(x) = x^2 for all x
      intro x y z
      -- Apply h_square to all terms
      repeat rw [h_square]

      -- Verify the algebraic identity
      ring
