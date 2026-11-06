import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_12747 (f : ℝ → ℝ) (hf : f = λ x => x + cos x - sqrt 3 * sin x)
  (k : ℝ) :
  k ∈ Icc (-1) 3 ↔ ∃ x, deriv f x = k := by

  have h1 : ∀ x, deriv f x = 1 - sin x - sqrt 3 * cos x := by
    intro x
    rw [hf]
    simp [deriv_add, deriv_sub, deriv_id'', mul_comm (sqrt 3)]
    <;> try field_simp
    <;> try ring
    all_goals linarith

  have h2 : -1 ≤ k ∧ k ≤ 3 ↔ ∃ x, deriv f x = k := by
    constructor
    · -- Forward direction: If k ∈ [-1, 3], then ∃ x, deriv f x = k
      intro h
      rcases h with ⟨h3, h4⟩
      use arcsin ((1 - k) / 2) - Real.pi / 3
      have h_eq : deriv f (arcsin ((1 - k) / 2) - Real.pi / 3) = 1 - sin (arcsin ((1 - k) / 2) - Real.pi / 3) - sqrt 3 * cos (arcsin ((1 - k) / 2) - Real.pi / 3) := h1 (arcsin ((1 - k) / 2) - Real.pi / 3)
      have eq2 : sin (arcsin ((1 - k) / 2) - Real.pi / 3) = sin (arcsin ((1 - k) / 2)) * cos (Real.pi / 3) - cos (arcsin ((1 - k) / 2)) * sin (Real.pi / 3) := by
        rw [sin_sub]
      have eq3 : cos (arcsin ((1 - k) / 2) - Real.pi / 3) = cos (arcsin ((1 - k) / 2)) * cos (Real.pi / 3) + sin (arcsin ((1 - k) / 2)) * sin (Real.pi / 3) := by
        rw [cos_sub]
      have h10 : sin (arcsin ((1 - k) / 2)) = (1 - k) / 2 := by
        rw [sin_arcsin]
        all_goals linarith
      have h11 : cos (arcsin ((1 - k) / 2)) = Real.sqrt (1 - ((1 - k) / 2) ^ 2) := by
        rw [cos_arcsin]
      have h12 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
        rw [sin_pi_div_three]
      have h13 : cos (Real.pi / 3) = 1 / 2 := by
        rw [cos_pi_div_three]
      rw [h_eq]
      rw [eq2, eq3, h10, h11, h12, h13]
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (1 - ((1 - k) / 2) ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - ((1 - k) / 2) ^ 2 by nlinarith), Real.sqrt_nonneg (3), Real.sqrt_nonneg (1 - ((1 - k) / 2) ^ 2) ]

    · -- Backward direction: If ∃ x, deriv f x = k, then k ∈ [-1, 3]
      intro h
      rcases h with ⟨x, hx⟩
      have h_eq : deriv f x = 1 - sin x - sqrt 3 * cos x := h1 x
      rw [h_eq] at hx
      have eq1 : sin x + sqrt 3 * cos x = 1 - k := by linarith

      have h3 : -2 ≤ 1 - k ∧ 1 - k ≤ 2 := by
        have h4 : (sin x + sqrt 3 * cos x) ^ 2 ≤ (4 : ℝ) := by
          nlinarith [Real.sin_sq_add_cos_sq x, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_nonneg (sin x * Real.sqrt 3 - cos x), sq_nonneg (sin x - sqrt 3 * cos x), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
        rw [eq1] at h4
        constructor
        · -- Prove -2 ≤ 1 - k
          nlinarith
        · -- Prove 1 - k ≤ 2
          nlinarith

      constructor
      · -- Prove -1 ≤ k
        linarith
      · -- Prove k ≤ 3
        linarith

  simp at h2 ⊢
  tauto