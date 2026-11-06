import Mathlib

theorem calculus_29084 (a b : ℝ) (f : ℝ → ℝ) (hf : f = fun x => 3 * x ^ 2 + 2 * a * x + b)
    (h : ∫ x in (-1)..1, |f x| < 2) :
    ∃ x y, x ≠ y ∧ f x = 0 ∧ f y = 0 := by
  by_cases h2 : a ^ 2 > 3 * b
  · -- If a^2 > 3b, then the discriminant is positive, so there are two distinct real roots.
    have h3 : (4 * a ^ 2 - 12 * b) > 0 := by
      nlinarith
    use (-2 * a + Real.sqrt (4 * a ^ 2 - 12 * b)) / 6, (-2 * a - Real.sqrt (4 * a ^ 2 - 12 * b)) / 6
    constructor
    · -- Show that x ≠ y.
      by_contra h_eq
      have h5 : Real.sqrt (4 * a ^ 2 - 12 * b) = 0 := by
        nlinarith
      have h6 : (4 * a ^ 2 - 12 * b) = (0 : ℝ) := by
        rw [Real.sqrt_eq_zero (by nlinarith)] at h5
        nlinarith
      nlinarith
    constructor
    · -- Show that f x = 0.
      rw [hf]
      simp
      nlinarith [Real.sqrt_nonneg (4 * a ^ 2 - 12 * b), Real.sq_sqrt (show 0 ≤ (4 * a ^ 2 - 12 * b : ℝ) by nlinarith)]
    · -- Show that f y = 0.
      rw [hf]
      simp
      nlinarith [Real.sqrt_nonneg (4 * a ^ 2 - 12 * b), Real.sq_sqrt (show 0 ≤ (4 * a ^ 2 - 12 * b : ℝ) by nlinarith)]
  · -- If a^2 ≤ 3b, then the discriminant is ≤ 0.
    have h3 : a ^ 2 ≤ 3 * b := by linarith
    have h4 : (4 * a ^ 2 - 12 * b) ≤ 0 := by
      nlinarith
    -- If the discriminant is ≤ 0, f(x) ≥ 0 for all x.
    have h5 : ∀ x : ℝ, f x ≥ 0 := by
      intro x
      have h6 : f x = 3 * x ^ 2 + 2 * a * x + b := by
        rw [hf]
      rw [h6]
      nlinarith [sq_nonneg (x + a / 3), sq_nonneg (a ^ 2 - 3 * b), sq_nonneg (3 * x + a), sq_nonneg (3 * (x + a / 3) ^ 2)]
    -- Then |f(x)| = f(x) for all x, and the integral is 2 + 2b.
    have h7 : ∫ x in (-1)..1, |f x| = 2 + 2 * b := by
      have h12 : ∀ x : ℝ, |f x| = f x := by
        intro x
        have h13 : f x ≥ 0 := h5 x
        rw [abs_of_nonneg h13]
      have h10 : ∫ x in (-1)..1, |f x| = ∫ x in (-1)..1, (f x : ℝ) := by
        congr
        funext x
        exact h12 x
      rw [h10]
      simp [hf]
      all_goals
        norm_num [intervalIntegral.integral_const, mul_comm]
        all_goals
          ring
    -- So 2 + 2b < 2, so b < 0.
    have h8 : 2 + 2 * b < 2 := by
      linarith [h7, h]
    -- But since f(x) ≥ 0 for all x, in particular f(0) = b ≥ 0.
    have h9 : b ≥ 0 := by
      have h10 : f 0 ≥ 0 := h5 0
      simp [hf] at h10
      linarith
    -- This contradicts b < 0.
    have h10 : b < 0 := by
      linarith
    linarith