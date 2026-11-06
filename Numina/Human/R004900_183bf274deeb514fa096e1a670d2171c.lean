import Mathlib

/- Let $n$ be a positive integer. Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ that satisfy the equation

$$
(f(x))^{n} f(x+y)=(f(x))^{n+1}+x^{n} f(y)
$$

for all $x, y \in \mathbb{R}$.-/
theorem algebra_604510 (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ) :
    (∀ x y, (f x) ^ n * f (x + y) = (f x) ^ (n + 1) + x ^ n * f y) ↔ ((∀ x, f x = 0) ∨ (∀ x, f x = x) ∨ (Even n ∧ ∀ x, f x = -x)) := by
  -- Break the goal into two parts.
  apply Iff.intro
  . -- First show that the functional equation implies the specific solutions.
    intro hf
    -- Get the value of f(0).
    have h₀ : f 0 = 0 := by
      -- Substitute (x, y) = (1, 0) into the functional equation.
      specialize hf 1 0
      simp [pow_add] at hf
      exact hf
    -- Explore f(-x) for x ≠ 0.
    have h₁ (x : ℝ) : x ≠ 0 → f x * (x ^ (n ^ 2 + 2 * n) - (f x) ^ (n ^ 2 + 2 * n)) = 0 := by
      intro hx
      -- Substitute (x, y) = (x, -x) into the functional equation.
      have hf' := hf x (-x)
      simp [h₀] at hf'
      replace hf' : f (-x) = -f x ^ (n + 1) / x ^ n := by
        field_simp
        linarith only [hf']
      -- Substitute (x, y) = (-x, x) into the functional equation.
      specialize hf (-x) x
      simp [h₀] at hf
      -- Combine the two equations.
      rw [hf', div_pow, neg_pow, pow_add] at hf
      field_simp at hf
      nth_rw 2 [neg_pow] at hf
      ring_nf at hf ⊢
      rw [<-neg_mul, <-add_mul] at hf
      simp at hf
      exact hf
    -- Analyze cases.
    by_cases h₂ : ∃ a ≠ 0, f a = 0
    . -- Suppose f(a) = 0 for some a ≠ 0.
      obtain ⟨a, ha, hfa⟩ := h₂
      -- Substitute (x, y) = (a, y) into the functional equation.
      have h₂ (y : ℝ) := hf a y
      -- We get that f(y) = 0 for all y.
      simp [hfa, zero_pow hn.ne', ha] at h₂
      tauto
    . -- Suppose f(a) ≠ 0 for all a ≠ 0.
      simp [<-ne_eq] at h₂
      -- Simplify h₁ by cancelling f(x) on both sides to get x ^ (n² + 2n) = (f(x)) ^ (n² + 2n).
      replace h₁ (x : ℝ) : x ≠ 0 → x ^ (n ^ 2 + 2 * n) = f x ^ (n ^ 2 + 2 * n) := by
        intro hx
        specialize h₁ x hx
        simp [h₂ x hx] at h₁
        exact eq_of_sub_eq_zero h₁
      -- Consider the parity of n.
      by_cases h₃ : Even n
      . -- Suppose n is even.
        right
        simp [h₃]
        -- Then n² + 2n is even.
        have h₄ : Even (n ^ 2 + 2 * n) := by
          apply Even.add
          rw [Nat.even_pow]
          simp [h₃]
          simp
        -- First show that f(x) = x or -x for each x ≠ 0.
        have h₅ (x : ℝ) : x ≠ 0 → f x = x ∨ f x = -x := by
          intro hx
          specialize h₁ x hx
          symm at h₁
          rw [pow_eq_pow_iff_of_ne_zero (by omega)] at h₁
          simp [h₄] at h₁
          exact h₁
        -- We could prove that f(x) = x for all x ≠ 0 or f(x) = -x for all x ≠ 0.
        by_cases h₆ : ∃ x ≠ 0, f x = x
        . -- Suppose f(x) = x for some x ≠ 0.
          obtain ⟨x, hx, hfx⟩ := h₆
          have h₆ : ∀ y, y ≠ 0 → f y = y := by
            -- Assume on the contrary that f(y) ≠ y for some y ≠ 0, we can derive a ccontradiction.
            by_contra!
            obtain ⟨y, hy, hfy⟩ := this
            have h₆ := h₅ y hy
            simp [hfy] at h₆
            -- Consider the original equation with this (x, y).
            specialize hf x y
            simp [hfx, h₆] at hf
            -- We have f(x + y) = x - y.
            replace hf : x ^ n * (f (x + y) - (x - y)) = 0 := by
              ring_nf at hf ⊢
              linarith
            simp [hx, hn.ne'] at hf
            apply eq_of_sub_eq_zero at hf
            -- Square both sides to get (x + y)² = (x - y)².
            replace hf := congr_arg (· ^ 2) hf
            simp at hf
            by_cases h₇ : x + y = 0
            . -- If x + y = 0, then x = y = 0, contradiction.
              symm at hf
              simp [h₇, h₀] at hf
              absurd hx
              linarith
            . -- If otherwise, we have f(x + y)² = (x + y)².
              have h₈ : f (x + y) ^ 2 = (x + y) ^ 2 := by
                rw [sq_eq_sq_iff_eq_or_eq_neg]
                exact h₅ (x + y) h₇
              -- We derive a contradiction from (x + y)² = (x - y)².
              have h₉ : x * y = 0 := by
                linarith
              simp [hx, hy] at h₉
          clear x hx hfx
          -- This corresponds to the case f(x) = x for all x.
          left
          intro x
          by_cases hx : x = 0
          . simp [hx, h₀]
          . exact h₆ x hx
        . -- This corresponds to the case f(x) = -x for all x.
          right
          simp [<-ne_eq] at h₆
          intro x
          by_cases hx : x = 0
          . simp [hx, h₀]
          . specialize h₆ x hx
            specialize h₅ x hx
            tauto
      . -- Suppose n is odd.
        right
        left
        intro x
        by_cases hx : x = 0
        . simp [hx, h₀]
        . specialize h₁ x hx
          rw [pow_eq_pow_iff_of_ne_zero (by omega)] at h₁
          -- Verify that n² + 2n is odd.
          have h₄ : ¬Even (n ^ 2 + 2 * n) := by
            simp at h₃ ⊢
            apply Odd.add_even
            exact Odd.pow h₃
            simp
          simp [h₄] at h₁
          linarith only [h₁]
  . -- Verify that the functions are indeed solutions to the equation.
    rintro (h | h | h)
    . -- Verify the case that f(x) = 0.
      simp [h]
    . -- Verify the case that f(x) = x.
      intro x y
      simp [h, pow_add]
      ring
    . -- Verify the case that f(x) = -x and n is even.
      obtain ⟨hn, h⟩ := h
      intro x y
      simp [h, pow_add, Even.neg_pow hn]
      ring