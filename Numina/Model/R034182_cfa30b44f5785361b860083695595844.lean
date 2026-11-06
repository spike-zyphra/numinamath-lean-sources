import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_253779 {x : ℝ} (hx : x ∈ Set.univ \ {x : ℝ | ∃ k : ℤ, x = (2 * k + 1) * π / 2}) :
    16 * (sin x)^2 - 9 * (tan x)^2 ≤ 1 := by
  rcases hx with ⟨hx1, hx2⟩
  have htan : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  have hc : cos x ≠ 0 := by
    by_contra h
    have h1 : ∃ k : ℤ, x = (2 * k + 1) * π / 2 := by
      have h' : cos x = 0 := h
      obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 h'
      refine ⟨k, by linarith [hk]⟩
    contradiction
  rw [htan]
  have h1 : 16 * (sin x) ^ 2 - 9 * (sin x / cos x) ^ 2 ≤ 1 := by
    have h2 : cos x ≠ 0 := hc
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    have h4 : 0 < cos x ^ 2 := by
      exact sq_pos_of_ne_zero h2
    have h5 : 16 * (sin x) ^ 2 - 9 * (sin x / cos x) ^ 2 - 1 ≤ 0 := by
      have h6 : 16 * (sin x) ^ 2 - 9 * (sin x / cos x) ^ 2 - 1 = (16 * (sin x) ^ 2 * (cos x) ^ 2 - 9 * (sin x) ^ 2 - (cos x) ^ 2) / ( (cos x) ^ 2 ) := by
        field_simp
        <;> ring
      rw [h6] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is non-positive
        nlinarith [ sq_nonneg (4 * (sin x) * (cos x) - 3 * (sin x) ), sq_nonneg (4 * (sin x) * (cos x) + 3 * (sin x) ), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - 1 / 4), sq_nonneg (cos x ^ 2 - 3 / 4) ]
      · -- Show that the denominator is non-negative
        positivity
    linarith
  linarith