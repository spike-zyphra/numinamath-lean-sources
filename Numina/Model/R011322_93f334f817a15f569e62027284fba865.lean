import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_8675 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin x - sin (2 * x) + sqrt 3) :
    IsLeast (range f) (-sqrt 3) ↔ False := by
  constructor
  ·
    intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨x, hx⟩
    have hfx : f x = -sqrt 3 := hx
    rw [hf] at hfx
    simp at hfx
    have h1 : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    rw [h1] at hfx
    have h2 : sin x * (1 - cos x) = -sqrt 3 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (0: ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (sin x - 0), sq_nonneg (sin x ^ 2 - (3 : ℝ) / 4), sq_nonneg (cos x + 1 / 2),
      Real.sqrt_nonneg 3,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
  ·
    intro h
    cases h