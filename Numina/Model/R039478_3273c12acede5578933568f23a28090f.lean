import Mathlib

theorem algebra_201896 {f : ℝ → ℝ} (h₀ : ∀ x y, f (x + y) = f x + f y + x * y + 2014)
    (h₁ : ∀ x, f (-x) = f x) :
    {x : ℝ | f x = 0} = {(2 * Real.sqrt 1007), (-2 * Real.sqrt 1007)} := by
  have f0 : f 0 = -2014 := by
    specialize h₀ 0 0
    norm_num at h₀
    linarith

  have eq1 : ∀ x : ℝ, f x = (x^2 / 2) - 2014 := by
    intro x
    have h2 := h₀ x (-x)
    have h3 : f (x + -x) = f x + f (-x) + x * (-x) + 2014 := by
      simpa using h2
    have h4 : f (x + -x) = f 0 := by
      simp
    rw [h4] at h3
    have h5 : f (-x) = f x := h₁ x
    rw [h5] at h3
    have h6 : f 0 = -2014 := f0
    rw [h6] at h3
    nlinarith

  have eq2 : ∀ x : ℝ, f x = 0 ↔ x^2 = 4028 := by
    intro x
    rw [eq1 x]
    constructor
    · -- If $\frac{x^2}{2} - 2014 = 0$ then $x^2 = 4028$
      intro h
      nlinarith
    · -- If $x^2 = 4028$ then $\frac{x^2}{2} - 2014 = 0$
      intro h
      nlinarith

  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have eq3 : f x = 0 ↔ x = (2 * Real.sqrt 1007) ∨ x = (-2 * Real.sqrt 1007) := by
    rw [eq2 x]
    constructor
    · -- Forward: x^2 = 4028 implies x = ±2√1007
      intro h_eq
      have h6 : x^2 = (2 * Real.sqrt 1007) ^2 := by
        nlinarith [Real.sqrt_nonneg 1007, Real.sq_sqrt (show (0 : ℝ) ≤ (1007 : ℝ) by norm_num)]
      have h7 : (x - (2 * Real.sqrt 1007)) * (x + (2 * Real.sqrt 1007)) = 0 := by
        nlinarith [Real.sqrt_nonneg 1007, Real.sq_sqrt (show (0 : ℝ) ≤ 1007 by norm_num)]
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- When $x - 2\sqrt{1007} = 0$, so $x = 2\sqrt{1007}$
        left
        linarith
      · -- When $x + 2\sqrt{1007} = 0$, so $x = -2\sqrt{1007}$
        right
        linarith
    · -- Backward: x = ±2√1007 implies x^2 = 4028
      rintro (h_eq | h_eq)
      · -- When $x = 2\sqrt{1007}$
        rw [h_eq]
        nlinarith [Real.sqrt_nonneg 1007, Real.sq_sqrt (show (0 : ℝ) ≤ 1007 by norm_num)]
      · -- When $x = -2\sqrt{1007}$
        rw [h_eq]
        nlinarith [Real.sqrt_nonneg 1007, Real.sq_sqrt (show (0 : ℝ) ≤ 1007 by norm_num)]
  simp [eq3]