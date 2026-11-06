import Mathlib

/- JPN   Find all functions $f$ from the set of real numbers into the set of real numbers which satisfy for all real $x, y$ the identity  $$ f(x f(x+y))=f(y f(x))+x^{2} $$ -/
theorem algebra_23811 (f : ℝ → ℝ) :
    (∀ x y, f (x * f (x + y)) = f (y * f x) + x ^ 2) ↔ ((∀ x, f x = x) ∨ (∀ x, f x = -x)) := by
  -- Break the goal into two implications.
  apply Iff.intro
  . intro h₀
    -- Show that f(0) = 0.
    have h₁ : f 0 = 0 := by
      by_contra!
      -- If f(0) ≠ 0, f is a constant.
      have h₁ (t : ℝ) : f t = f 0 := by
        have h₂ : f (0 * f (0 + t / f 0)) = f (t / f 0 * f 0) + 0 ^ 2 := h₀ 0 (t / f 0)
        simp [this] at h₂
        rw [h₂]
      have h₂ (x : ℝ) : x = 0 := by
        have h₃ : f (x * f (x + 0)) = f (0 * f x) + x ^ 2 := h₀ x 0
        simp [h₁ (x * f x)] at h₃
        exact h₃
      absurd h₂
      simp
      use 1
      norm_num
    have h₂ (t : ℝ) := h₀ t 0
    simp [h₁] at h₂
    have h₃ (t : ℝ) := h₀ t (-t)
    simp [h₁] at h₃
    -- Show that f(t) = 0 ↔ t = 0.
    have h₄ (t : ℝ) : f t = 0 → t = 0 := by
      intro h₄
      have h₅ := h₀ t 0
      simp [h₄] at h₅
      exact h₅
    -- Show that f is odd.
    have h₅ (s : ℝ) : f s = -f (-s) := by
      by_cases h₅ : f s = 0
      . apply h₄ s at h₅
        subst s
        simp [h₁]
      . rw [<-ne_eq, ne_iff_lt_or_gt] at h₅
        cases h₅ with
        | inl h₅ =>
          -- Let t be a number such that f(s) = -t².
          let t := Real.sqrt (-f s)
          have h₆ : f s = -t ^ 2 := by
            simp [t]
            rw [Real.sq_sqrt]
            simp
            linarith only [h₅]
          have h₇ : f t ≠ 0 := by
            by_contra! h₇
            apply h₄ t at h₇
            rw [h₇] at h₆
            linarith only [h₅, h₆]
          -- Let a be a number such that af(t) = s.
          let a := s / f t
          have h₈ : a * f t = s := by
            simp [a]
            rw [div_mul_cancel₀]
            exact h₇
          -- Substitute (x, y) = (t, a) into the original equation.
          have h₉ := h₀ t a
          simp [h₈, h₆] at h₉
          apply h₄ at h₉
          simp at h₉
          cases h₉ with
          | inl h₉ =>
            rw [h₉] at h₆
            linarith only [h₅, h₆]
          | inr h₉ =>
            apply h₄ at h₉
            rw [add_comm, add_eq_zero_iff_eq_neg] at h₉
            simp [h₉] at h₈
            simp [<-h₈, h₂ t]
            linarith only [h₃ t]
        | inr h₅ =>
          -- Let t be a number such that f(s) = t².
          let t := Real.sqrt (f s)
          have h₆ : f s = t ^ 2 := by
            simp [t]
            rw [Real.sq_sqrt]
            linarith only [h₅]
          have h₇ : t ≠ 0 := by
            by_contra! h₇
            rw [h₇] at h₆
            linarith only [h₅, h₆]
          have h₈ : f t ≠ 0 := by
            contrapose! h₇
            exact h₄ t h₇
          have h₉ : s ≠ 0 := by
            by_contra! h₉
            subst h₉
            linarith only [h₁, h₅]
          -- Let a be a number such that tf(a) = s.
          let a' := Real.sqrt |s / t|
          let a := if s / t > 0 then a' * f a' else -a' * f a'
          have h₁₀ : t * f a = s := by
            have h₁₀ : s / t ≠ 0 := by
              simp [h₇, h₉]
            rw [ne_iff_lt_or_gt, or_comm] at h₁₀
            cases h₁₀ with
            | inl h₁₀ =>
              simp [a]
              rw [if_pos h₁₀]
              rw [h₂]
              simp [a', abs, le_of_lt h₁₀]
              rw [mul_div_cancel₀ _ h₇]
            | inr h₁₀ =>
              simp [a]
              replace h₁₀ : ¬s / t > 0 := by
                rw [not_lt]
                exact le_of_lt h₁₀
              rw [if_neg h₁₀]
              rw [show f (-(a' * f a')) = -a' ^ 2 by linarith only [h₃ a']]
              simp at h₁₀
              simp [a', abs, h₁₀]
              rw [mul_div_cancel₀ _ h₇]
          -- Substitute (x, y) = (t, a - t) into the original equation.-
          have h₁₁ := h₀ t (a - t)
          simp [h₁₀, <-h₆] at h₁₁
          apply h₄ at h₁₁
          simp [h₈] at h₁₁
          rw [show t = a by linarith only [h₁₁]] at h₁₀
          rw [<-h₁₀, h₂ a]
          linarith only [h₃ a]
    have h₅ (s : ℝ) : f (-s) = -f s := by
      linarith only [h₅ s]
    -- Substitute (x, y) = (s, t), (x, y) = (t, -s - t), (x, y) = (-s - t, s) into the original equation.
    have h₆ (s t : ℝ) := h₀ s t
    have h₇ (s t : ℝ) := h₀ t (-(s + t))
    have h₈ (s t : ℝ) := h₀ (-(s + t)) s
    replace h₇ (s t : ℝ) : -f (t * f s) = -f ((s + t) * f t) + t ^ 2 := by
      specialize h₇ s t
      rw [neg_mul, h₅] at h₇
      simp [h₅] at h₇
      exact h₇
    replace h₈ (s t : ℝ) : f ((s + t) * f t) = -f (s * f (s + t)) + (s + t) ^ 2 := by
      specialize h₈ s t
      rw [neg_mul, h₅, h₅, mul_neg, h₅, neg_sq] at h₈
      simp [h₅] at h₈
      exact h₈
    -- Adding these three equations together, we get f(tf(s)) = ts for all s, t ∈ ℝ.
    have h₉ (s t : ℝ) : f (t * f s) = t * s := by
      linarith only [h₆ s t, h₇ s t, h₈ s t]
    let s := f 1
    have h₁₀ : f s = 1 := by
      specialize h₂ 1
      simp at h₂
      simp [s, h₂]
    replace h₉ (t : ℝ) : f t = t * s := by
      specialize h₉ s t
      simp [h₁₀] at h₉
      exact h₉
    -- Show that s² = 1.
    specialize h₀ s 0
    simp [h₁₀, h₁] at h₀
    replace h₀ : (s - 1) * (s + 1) = 0 := by
      linarith only [h₀]
    simp at h₀
    cases h₀ with
    | inl h₁₁ =>
      replace h₁₁ : s = 1 := by
        linarith only [h₁₁]
      simp [h₁₁] at h₉
      left
      exact h₉
    | inr h₁₁ =>
      replace h₁₁ : s = -1 := by
        linarith only [h₁₁]
      simp [h₁₁] at h₉
      right
      exact h₉
  . -- Show that f(x) = x and f(x) = -x satisfy the condition.
    rintro (h | h) x y
    . rw [h, h, h, h]
      ring_nf
    . rw [h, h, h, h]
      ring_nf
