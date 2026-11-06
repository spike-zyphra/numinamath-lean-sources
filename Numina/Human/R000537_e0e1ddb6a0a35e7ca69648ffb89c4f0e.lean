import Mathlib

/- If \[f(x) =
\begin{cases}
x^2-4 &\quad \text{if } x \ge -4, \\
x + 3 &\quad \text{otherwise},
\end{cases}
\]then for how many values of $x$ is $f(f(x)) = 5$? -/
theorem algebra_1392 {f : ℝ → ℝ} (hf : ∀ x, x ≥ -4 → f x = x ^ 2 - 4) (hf' : ∀ x, x < -4 → f x = x + 3) :
    {x | f (f x) = 5}.encard = 5 := by
  -- {1, -1, √7, -√7, -6} has cardinality 5.
  have h₀ : ({1, -1, Real.sqrt 7, -Real.sqrt 7, -6} : Set ℝ).ncard = 5 := by
    -- A small technical lemma for the ease of simplification of the following.
    have h₀ (a b : ℝ) : b > 0 → a ≠ b ^ 2 → ¬b = Real.sqrt a := by
      intro g₀ g₁
      by_contra! g₂
      symm at g₂
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos] at g₂
      rw [<-g₂, pow_two] at g₁
      tauto
      apply g₀
    have h₁ (a b : ℝ) : b > 0 → a ≠ b ^ 2 → ¬b = -Real.sqrt a := by
      intro g₀ _
      by_contra! g₂
      symm at g₂
      linarith only [show 0 ≤ Real.sqrt a by apply Real.sqrt_nonneg, g₀, g₂]
    have h₂ (a b : ℝ) : b > 0 → a ≠ b ^ 2 → ¬-b = Real.sqrt a := by
      intro g₀ _
      by_contra! g₂
      symm at g₂
      linarith only [show 0 ≤ Real.sqrt a by apply Real.sqrt_nonneg, g₀, g₂]
    have h₃ (a : ℝ) : a > 0 → ¬Real.sqrt a = -Real.sqrt a := by
      intro g₀
      by_contra! g₁
      replace g₁ : Real.sqrt a = 0 := by
        linarith only [g₁]
      apply Real.sqrt_pos_of_pos at g₀
      linarith only [g₀, g₁]
    calc
      Set.ncard {1, -1, Real.sqrt 7, -Real.sqrt 7, -6} = Set.ncard {-1, Real.sqrt 7, -Real.sqrt 7, -6} + 1 := by rw [Set.ncard_insert_of_not_mem (by simp; refine ⟨by norm_num, by apply h₀; norm_num; norm_num, by apply h₁; norm_num; norm_num, by norm_num⟩)]
      _ = Set.ncard {Real.sqrt 7, -Real.sqrt 7, -6} + 1 + 1 := by rw [Set.ncard_insert_of_not_mem (by simp; refine ⟨by apply h₂; norm_num; norm_num, by apply h₀; norm_num; norm_num⟩)]
      _ = Set.ncard {-Real.sqrt 7, -6} + 1 + 1 + 1 := by rw [Set.ncard_insert_of_not_mem (by simp; refine ⟨by apply h₃; norm_num, by specialize h₂ 7 6 (by norm_num) (by norm_num); tauto⟩)]
      _ = Set.ncard ({-6} : Set ℝ) + 1 + 1 + 1 + 1 := by rw [Set.ncard_insert_of_not_mem (by simp; specialize h₀ 7 6 (by norm_num) (by norm_num); tauto)]
      _ = 1 + 1 + 1 + 1 + 1 := by rw [Set.ncard_singleton]
      _ = 5 := by norm_num
  replace h₀ : ({1, -1, Real.sqrt 7, -Real.sqrt 7, -6} : Set ℝ).encard = 5 := by
    rw [Set.Finite.encard_eq_coe, <-Set.ncard_def, h₀]
    simp
    apply Set.finite_of_ncard_pos
    rw [h₀]
    norm_num
  suffices h : {x | f (f x) = 5} = {1, -1, Real.sqrt 7, -Real.sqrt 7, -6} by
    rw [h]
    exact h₀
  -- Now it suffices to prove that {x | f (f x) = 5} = {1, -1, Real.sqrt 7, -Real.sqrt 7, -6}.
  ext x
  apply Iff.intro
  <;> intro h
  <;> simp at h ⊢
  . -- If f(f(x)) = 5, then x = 1 or -1 or √7 or -√7 or -6.
    have h₁ : f x ≥ -4 := by
      -- If f(x) < -4, we get a contradiction.
      by_contra! h₁
      rw [hf' (f x) h₁] at h
      linarith only [h, h₁]
    rw [hf (f x) h₁] at h
    replace h : f x ^ 2 = 3 ^ 2 := by
      linarith only [h]
    apply eq_or_eq_neg_of_sq_eq_sq at h
    obtain h | h := h
    . -- Suppose f(3) = 3.
      have h₂ : x ≥ -4 := by
        -- If x < -4, we get a contradiction.
        by_contra! h₂
        rw [hf' x h₂] at h
        linarith only [h, h₂]
      rw [hf x h₂] at h
      replace h : x ^ 2 = Real.sqrt 7 ^ 2 := by
        rw [Real.sq_sqrt]
        linarith only [h]
        norm_num
      apply eq_or_eq_neg_of_sq_eq_sq at h
      -- We get x = √7 or -√7.
      obtain h | h := h
      . right
        right
        left
        exact h
      . right
        right
        right
        left
        exact h
    . -- Suppose f(3) = -3.
      by_cases h₂ : x < -4
      . -- Suppose x < -4.
        rw [hf' x h₂] at h
        -- We get x = -6.
        right
        right
        right
        right
        linarith only [h]
      . -- Suppose x ≥ -4.
        simp at h₂
        rw [hf x h₂] at h
        replace h : x ^ 2 = 1 ^ 2 := by
          linarith only [h]
        apply eq_or_eq_neg_of_sq_eq_sq at h
        -- We get x = 1 or -1.
        obtain h | h := h
        . left
          exact h
        . right
          left
          exact h
  . -- If x = 1 or -1 or √7 or -√7 or -6, then f(f(x)) = 5.
    obtain h | h | h | h | h := h
    . rw [h, hf 1, hf]
      all_goals
        norm_num
    . rw [h, hf (-1), hf]
      all_goals
        norm_num
    . rw [h, hf (Real.sqrt 7), hf]
      all_goals
        norm_num
      linarith only [show 0 ≤ Real.sqrt 7 by exact Real.sqrt_nonneg 7]
    . rw [h, hf (-Real.sqrt 7), hf]
      all_goals
        norm_num
      rw [Real.sqrt_le_left]
      all_goals
        norm_num
    . rw [h, hf' (-6), hf]
      all_goals
        norm_num
