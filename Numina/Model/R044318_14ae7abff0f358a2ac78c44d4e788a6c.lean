import Mathlib

open BigOperators Real Set

theorem calculus_81194 {f : ℝ → ℝ} (hf : f = λ x => x ^ 3 - x) :
    ∀ a > 0, ∃ x, f (a + x) = f x ↔ 0 < a ∧ a ≤ 2 := by
  intro a ha
  by_cases h : a ≤ 2
  · -- If a ≤ 2, then the discriminant is non-negative.
    use (-3 * a + Real.sqrt (12 - 3 * a ^ 2)) / 6
    constructor
    · -- Assume f(a + x) = f(x), prove 0 < a ∧ a ≤ 2
      intro h_eq
      constructor
      · linarith
      · linarith
    · -- Assume 0 < a ∧ a ≤ 2, prove f(a + x) = f(x)
      rintro ⟨ha1, ha2⟩
      have h_eq : (a + (-3 * a + Real.sqrt (12 - 3 * a ^ 2)) / 6) ^ 3 - (a + (-3 * a + Real.sqrt (12 - 3 * a ^ 2)) / 6) = ((-3 * a + Real.sqrt (12 - 3 * a ^ 2)) / 6) ^ 3 - ((-3 * a + Real.sqrt (12 - 3 * a ^ 2)) / 6) := by
        have h_eq3 : 3 * ((-3 * a + Real.sqrt (12 - 3 * a ^ 2)) / 6) ^ 2 + 3 * a * ((-3 * a + Real.sqrt (12 - 3 * a ^ 2)) / 6) + (a^2 - 1) = 0 := by
          nlinarith [Real.sqrt_nonneg (12 - 3 * a ^ 2), Real.sq_sqrt (show 0 ≤ (12 - 3 * a ^ 2 : ℝ) by nlinarith)]
        nlinarith [Real.sqrt_nonneg (12 - 3 * a ^ 2), Real.sq_sqrt (show 0 ≤ (12 - 3 * a ^ 2 : ℝ) by nlinarith)]
      simp [hf]
      linarith [h_eq]
  · -- If a > 2
    have h2 : a > 2 := by linarith
    use (0 : ℝ)
    constructor
    · -- Assume f(a + 0) = f(0), prove 0 < a ∧ a ≤ 2
      intro h_eq
      have h_eq2 : a ^ 3 - a = (0 : ℝ) ^ 3 - (0 : ℝ) := by
        simp [hf] at h_eq ⊢
        linarith
      have h_eq3 : a * (a ^ 2 - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h_eq3) with ha1 ha2
      · -- a = 0
        linarith
      · -- a ^ 2 - 1 = 0
        nlinarith [show a ^ 2 - 1 > 0 by nlinarith]
    · -- Assume 0 < a ∧ a ≤ 2, prove f(a + 0) = f(0)
      intro h
      exfalso
      linarith