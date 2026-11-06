import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_235597 (k : ℝ) :
  (∃ x : ℝ, (1 + sin x) / (2 + cos x) ≥ k) ↔ k ≤ 4 / 3 := by
  constructor
  · -- Assume there exists an `x` such that (1 + sin x) / (2 + cos x) ≥ k, then k ≤ 4 / 3
    intro h
    rcases h with ⟨x, hx⟩
    by_contra h1
    push_neg at h1
    have h2 : (1 + sin x) / (2 + cos x) ≥ k := hx
    have h3 : 2 + cos x > 0 := by
      have h4 : -1 ≤ cos x := by linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
      have h5 : cos x ≤ 1 := by linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
      nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]
    have h6 : (1 + sin x) ≥ k * (2 + cos x) := by 
      have h7 : (2 + cos x) > 0 := h3
      apply (le_div_iff₀ h7).mp at h2
      linarith
    -- We have the inequality $1 + \sin x \geq k(2 + \cos x)$.
    -- Now, we substitute an upper bound: $k > 4/3$.
    -- Show this leads to a contradiction.
    nlinarith [sq_nonneg (sin x - 4 / 3), sq_nonneg (cos x - 5 / 3), sq_nonneg (sin x - 0), sq_nonneg (cos x - 1), sq_nonneg (k), sq_nonneg (k - 4 / 3), Real.sin_sq_add_cos_sq x, Real.sin_le_one x, Real.cos_le_one x, Real.neg_one_le_sin x, Real.neg_one_le_cos x, mul_self_nonneg (cos x - (5 / 3)), mul_self_nonneg (sin x - (3 / 5)), mul_self_nonneg (cos x - (- 3 / 5)), Real.sin_sq_add_cos_sq x, sq_nonneg (k - 4 / 3), sq_nonneg (3 * sin x - 4 * cos x), sq_nonneg (4 * cos x - 3 * sin x + 2)]
  · -- Now for the reverse implication: if k ≤ 4 / 3, then there exists x such that (1 + sin x) / (2 + cos x) ≥ k
    intro h
    by_cases h1 : k ≤ 4 / 3
    · -- k ≤ 4 / 3
      use Real.pi - Real.arcsin (3 / 5)
      have h11 : sin (Real.pi - Real.arcsin (3 / 5)) = 3 / 5 := by 
        rw [sin_pi_sub]
        have h16 : sin (Real.arcsin (3 / 5)) = 3 / 5 := by 
          apply Real.sin_arcsin
          all_goals norm_num
        rw [h16]
      have h12 : cos (Real.pi - Real.arcsin (3 / 5)) = -4 / 5 := by
        rw [cos_pi_sub]
        have h16 : cos (Real.arcsin (3 / 5)) = 4 / 5 := by
          have h112 : cos (Real.arcsin (3 / 5)) = Real.sqrt (1 - (3 / 5) ^ 2) := by 
            rw [Real.cos_arcsin]
          have h113 : Real.sqrt (1 - (3 / 5) ^ 2) = 4 / 5 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h112, h113]
        linarith
      rw [h11, h12]
      norm_num at *
      all_goals linarith
    · -- k > 4 / 3
      linarith