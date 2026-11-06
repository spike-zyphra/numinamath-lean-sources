import Mathlib

open Real Set
open scoped Real

theorem algebra_230491 {x : ℝ} :
  sin x ^ 2 + 1 = cos (sqrt 2 * x) ↔ x = 0 := by
  constructor
  · -- Forward direction: from the equation to x = 0
    intro h
    have h1 : sin x ^ 2 = 0 := by
      have h2 : sin x ^ 2 ≥ 0 := by apply sq_nonneg
      have h3 : cos (sqrt 2 * x) ≤ 1 := by apply cos_le_one
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h4 : sin x = 0 := by
      nlinarith
    have h5 : cos (sqrt 2 * x) = 1 := by
      linarith [h, h4]
    have h6 : ∃ n : ℤ, x = ↑n * π := by
      have h7 : sin x = 0 := h4
      obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h7
      use n
      linarith
    rcases h6 with ⟨n, hn⟩
    have h7 : cos (sqrt 2 * (↑n * π)) = 1 := by
      rw [show sqrt 2 * (↑n * π) = sqrt 2 * x by rw [hn]; all_goals ring] at *
      all_goals linarith [h5]
    have h8 : ∃ k : ℤ, sqrt 2 * (↑n * π) = 2 * ↑k * π := by
      have h9 : cos (sqrt 2 * (↑n * π)) = 1 := h7
      rw [cos_eq_one_iff] at h9
      rcases h9 with ⟨k, hk⟩
      refine ⟨k, by linarith [hk]⟩
    rcases h8 with ⟨k, hk⟩
    have hp : π ≠ 0 := Real.pi_ne_zero
    have h9 : sqrt 2 * (↑n : ℝ) = 2 * (↑k : ℝ) := by
      apply (mul_left_inj' hp).mp
      linarith [hk]
    have h10 : n = 0 := by
      by_cases h11 : n = 0
      · -- If n is 0, then clearly sqrt 2 * 0 = 0 = 2 * k implies k = 0
        exact_mod_cast h11
      · -- If n is not 0, we derive a contradiction that sqrt 2 is rational
        have h12 : n ≠ 0 := by
          exact_mod_cast h11
        have h14 : ∃ r : ℚ, (sqrt 2 : ℝ) = ↑r := by
          use (↑(2 * k) / ↑n)
          field_simp at *
          <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h12]
          all_goals norm_num at h12 ⊢
          <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        rcases h14 with ⟨r, hr⟩
        have h15 : Irrational (sqrt 2) := by
          apply irrational_sqrt_two
          all_goals norm_num
        have h16 : ¬ Irrational (sqrt 2) := by
          rw [show (sqrt 2 : ℝ) = ↑r by linarith [hr]]
          simp
        exfalso
        exact h16 h15
    have hn0 : (n : ℝ) = 0 := by
      exact_mod_cast h10
    rw [hn0] at hn
    have hx0 : x = 0 := by
      linarith [hn, Real.pi_pos]
    exact_mod_cast hx0
  · -- Backward direction: x = 0 implies the equation
    intro h
    rw [h]
    norm_num
    <;> ring_nf <;> norm_num [Real.sq_sqrt]