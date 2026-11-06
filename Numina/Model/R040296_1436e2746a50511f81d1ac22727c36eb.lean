import Mathlib

theorem algebra_285276 {f : ℝ → ℝ}
    (h₀ : f 0 ≠ 0)
    (h₁ : ∀ x > 0, f x > 1)
    (h₂ : ∀ a b, f (a + b) = f a * f b) :
    f 0 = 1 ∧
    (∀ x, f x > 0) ∧
    StrictMono f ∧
    {x | f x * f (2 * x - x ^ 2) > 1} = {x | x ∈ Set.Ioo 0 3} := by
  have h3 : f 0 = 1 := by
    have eq1 : f 0 = f 0 * f 0 := by
      specialize h₂ 0 0
      norm_num at h₂
      linarith
    have eq2 : f 0 * (f 0 - 1) = 0 := by
      linarith
    cases (mul_eq_zero.mp eq2) with
    | inl h =>
      exfalso
      exact h₀ h
    | inr h =>
      linarith
  have h4 : ∀ x, f x > 0 := by
    intro x
    by_cases h : x > 0
    · -- Positive $x$ where $h$ divides real variable R it must work with weaker h₁.
      specialize h₁ x h
      linarith
    by_cases h' : x < 0
    · -- Negative $x$, so let me make reciprocal use $f$.
      have h₃ : -x > 0 := by linarith
      have h₄ : f (-x) > 1 := h₁ (-x) h₃
      have h5 : f 0 = f x * f (-x) := by
        specialize h₂ x (-x)
        rw [show x + -x = (0 : ℝ) by linarith] at h₂
        linarith
      rw [h3] at h5
      have hx1 : f x > 0 := by
        nlinarith
      linarith
    · -- Zero. this would not work in given system before weights.
      have hx0 : x = 0 := by 
        linarith
      rw [hx0]
      linarith [h3]
  
  have h5 : StrictMono f := by
    intro x y h6
    have h7 : y - x > 0 := by linarith
    have h8 : f (y - x) > 1 := h₁ (y - x) h7
    have h9 : f y = f x * f (y - x) := by
      specialize h₂ x (y - x)
      rw [show x + (y - x) = (y : ℝ) by linarith] at h₂
      linarith
    nlinarith [h4 x, h8]

  have h6 : {x | f x * f (2 * x - x ^ 2) > 1} = {x | x ∈ Set.Ioo 0 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
    constructor
    · -- Assume f(x) * f(2x - x ^ 2) > 1, prove x in (0, 3).
      intro h
      have h7 : f x * f (2 * x - x ^ 2) = f (3 * x - x^2) := by
        have h8 : f (3 * x - x^2) = f (x + (2 * x - x ^ 2)) := by
          ring_nf
        rw [h8]
        have h9 : f (x + (2 * x - x ^ 2)) = f x * f (2 * x - x ^ 2) := by
          apply h₂
        linarith
      rw [h7] at h
      have h8 : 3 * x - x^2 > 0 := by
        by_contra h9
        push_neg at h9
        by_cases h10 : 3 * x - x^2 < 0
        · -- Contradicts by f 0 < 1.
          have h11 : f (3 * x - x ^ 2) < 1 := by
            have h12 : 3 * x - x^2 < 0 := by linarith
            have h13 : f (3 * x - x ^ 2) < f (0 : ℝ) := by
              apply h5
              linarith
            rw [show f (0 : ℝ) = 1 by linarith [h3]] at h13
            linarith
          linarith -- contradicts hypothesis
        · -- Contradicts with equality excess as function with strict 0.
          have h10 : 3 * x - x^2 = 0 := by linarith
          have h11 : f (3 * x - x^2) = 1 := by
            rw [show (3 * x - x ^ 2 : ℝ) = (0 : ℝ) by linarith]
            linarith [h3]
          linarith -- contradicts hypothesis
      have hx1 : 0 < x := by
        nlinarith [h8]
      have hx2 : x < 3 := by
        nlinarith [h8]
      constructor
      · linarith
      · linarith

    · -- Assume x in (0, 3), prove f(x) * f(2x - x^2) > 1.
      rintro ⟨hx1, hx2⟩
      have h7 : f x * f (2 * x - x^2) = f (3 * x - x^2) := by
        have h8 : f (3 * x - x^2) = f (x + (2 * x - x ^ 2)) := by
          ring_nf
        rw [h8]
        have h9 : f (x + (2 * x - x ^ 2)) = f x * f (2 * x - x ^ 2) := by
          apply h₂
        linarith
      have h8 : 3 * x - x^2 > 0 := by
        nlinarith
      have h9 : f (3 * x - x^2) > 1 := h₁ (3 * x - x^2) h8
      nlinarith [h7, h9]

  exact ⟨h3, h4, h5, h6⟩