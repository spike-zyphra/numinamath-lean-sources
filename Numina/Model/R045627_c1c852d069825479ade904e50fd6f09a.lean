import Mathlib

open Real

theorem inequalities_253925 (f : ℝ) :
    (∀ x y z w : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) →
      (6 * x * y + 5 * y * z + 6 * z * w) / (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) ≤ f) ↔
    f ≥ 9 / 2 := by
  constructor
  · -- Assume the inequality holds for all x, y, z, w, prove f ≥ 9/2
    intro h
    have h1 := h 2 3 3 2 (by norm_num)
    norm_num at h1
    linarith
  · -- Assume f ≥ 9/2, prove the inequality holds
    intro hf x y z w h
    have h1 : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 > 0 := by
      by_contra h2
      push_neg at h2
      have h21 : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 0 := by
        nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have hx2 : x ^ 2 = 0 := by
        nlinarith [h21, sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have hy2 : y ^ 2 = 0 := by
        nlinarith [h21, sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have hz2 : z ^ 2 = 0 := by
        nlinarith [h21, sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have hw2 : w ^ 2 = 0 := by
        nlinarith [h21, sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have hx3 : x = 0 := pow_eq_zero hx2
      have hy3 : y = 0 := pow_eq_zero hy2
      have hz3 : z = 0 := pow_eq_zero hz2
      have hw3 : w = 0 := pow_eq_zero hw2
      cases h with
      | inl hne =>
        contradiction
      | inr hne =>
        cases hne with
        | inl hne =>
          contradiction
        | inr hne =>
          cases hne with
          | inl hne =>
            contradiction
          | inr hne =>
            contradiction

    have h2 : 6 * x * y + 5 * y * z + 6 * z * w ≤ (9 / 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
      nlinarith [sq_nonneg (3 * x - 2 * y), sq_nonneg (3 * w - 2 * z), sq_nonneg (y - z), sq_nonneg (3*x - 2*y), sq_nonneg (2*z - 3*w), sq_nonneg (y - z)]

    have h3 : (6 * x * y + 5 * y * z + 6 * z * w) / (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) ≤ f := by
      have h4 : (6 * x * y + 5 * y * z + 6 * z * w) / (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) ≤ (9 / 2 : ℝ) := by
        apply (div_le_iff₀ (by positivity)).mpr
        linarith [h2]
      have h42 : (9 / 2 : ℝ) ≤ f := by linarith
      linarith [h4, h42]
    exact h3