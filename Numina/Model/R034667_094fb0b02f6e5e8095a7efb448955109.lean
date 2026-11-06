import Mathlib

open Real Set
open scoped Real

theorem calculus_12925 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sin x ^ 4 - sin x * cos x + cos x ^ 4) :
  range f = {y | 0 ≤ y ∧ y ≤ 9 / 8} := by
  have h1 : ∀ x, f x = 1 - (1/2) * (sin (2 * x)) ^ 2 - (1/2) * (sin (2 * x)) := by
    intro x
    rw [h₀]
    have h2 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x ^ 2 * cos x ^ 2) := by
      calc
        sin x ^ 4 + cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x ^ 2 * cos x ^ 2) := by ring
        _ = 1 ^ 2 - 2 * (sin x ^ 2 * cos x ^ 2) := by rw [Real.sin_sq_add_cos_sq x]
        _ = 1 - 2 * (sin x ^ 2 * cos x ^ 2) := by ring
    have h3 : sin x * cos x = (1 / 2) * sin (2 * x) := by
      have h4 : sin (2 * x) = 2 * sin x * cos x := by rw [sin_two_mul]
      linarith
    have h5 : sin x ^ 4 - sin x * cos x + cos x ^ 4 = (sin x ^ 4 + cos x ^ 4) - (sin x * cos x) := by ring
    calc
      sin x ^ 4 - sin x * cos x + cos x ^ 4 = (sin x ^ 4 + cos x ^ 4) - (sin x * cos x) := by ring
      _ = (1 - 2 * (sin x ^ 2 * cos x ^ 2)) - (sin x * cos x) := by rw [h2]
      _ = (1 - 2 * ((sin x * cos x) ^ 2)) - (sin x * cos x) := by ring
      _ = (1 - 2 * ((1 / 2) * sin (2 * x)) ^ 2) - ((1 / 2) * sin (2 * x)) := by rw [h3]
      _ = 1 - (1 / 2) * (sin (2 * x)) ^ 2 - (1 / 2) * (sin (2 * x)) := by ring

  ext y
  simp only [mem_range, mem_setOf_eq, exists_prop]
  constructor
  · -- First, prove that if y in range f, then 0 ≤ y ≤ 9/8.
    rintro ⟨x, hx⟩
    have h2 : 0 ≤ f x ∧ f x ≤ 9 / 8 := by
      have h6 : f x = 1 - (1/2) * (sin (2 * x)) ^ 2 - (1/2) * (sin (2 * x)) := h1 x
      have h7 : -1 ≤ sin (2 * x) ∧ sin (2 * x) ≤ 1 := by
        constructor
        · apply neg_one_le_sin
        · apply sin_le_one
      have h8 : 0 ≤ f x := by
        rw [h6]
        nlinarith [sq_nonneg (sin (2 * x) + 1 / 2), Real.sin_le_one (2 * x), Real.neg_one_le_sin (2 * x)]
      have h9 : f x ≤ 9 / 8 := by
        rw [h6]
        nlinarith [sq_nonneg (sin (2 * x) + 1 / 2), Real.sin_le_one (2 * x), Real.neg_one_le_sin (2 * x)]
      constructor
      · linarith
      · linarith
    have h9 : 0 ≤ y ∧ y ≤ 9 / 8 := by
      have h9 : f x = y := by
        linarith [hx]
      constructor
      · linarith [h2.1, h9]
      · linarith [h2.2, h9]
    tauto
  · -- Now prove the reverse.
    rintro ⟨hy1, hy2⟩
    have h12 : ∃ s, -1 ≤ s ∧ s ≤ 1 ∧ (1 - (1/2) * s ^ 2 - (1/2) * s ) = y := by
      use (-1 / 2 + Real.sqrt (9 - 8 * y) / 2)
      constructor
      · -- Show -1 ≤ s.
        nlinarith [Real.sqrt_nonneg (9 - 8 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 9 - 8 * y by nlinarith)]
      constructor
      · -- Show s ≤ 1.
        nlinarith [Real.sqrt_nonneg (9 - 8 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 9 - 8 * y by nlinarith)]
      · -- Show (1 - (1/2) * s ^ 2 - (1/2) * s ) = y
        nlinarith [Real.sqrt_nonneg (9 - 8 * y), Real.sq_sqrt (show (0 : ℝ) ≤ 9 - 8 * y by nlinarith)]
    rcases h12 with ⟨s, hs1, hs2, heq⟩
    have h14 : ∃ x, sin (2 * x) = s := by
      use (Real.arcsin s) / 2
      have h15 : sin (2 * ((Real.arcsin s) / 2)) = s := by
        have h16 : 2 * ((Real.arcsin s) / 2) = Real.arcsin s := by ring
        rw [h16]
        rw [Real.sin_arcsin]
        all_goals linarith [hs1, hs2]
      linarith [h15]
    rcases h14 with ⟨x, hx1⟩
    use x
    have h7 : f x = y := by
      have h6 : f x = 1 - (1/2) * (sin (2 * x)) ^ 2 - (1/2) * (sin (2 * x)) := h1 x
      rw [h6]
      rw [hx1]
      all_goals
        linarith [heq]
    linarith [h7]