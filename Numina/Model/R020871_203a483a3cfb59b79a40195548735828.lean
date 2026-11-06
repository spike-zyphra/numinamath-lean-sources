import Mathlib

open Real Set

lemma lemma_1 (x : ℝ) (hx : x ∈ Icc (-π) π) :
    sqrt (2 + 2 * cos x) = 2 * cos (x / 2) := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : -π ≤ x := by linarith
  have h2 : x ≤ π := by linarith
  have h3 : cos (x / 2) ≥ 0 := by
    apply cos_nonneg_of_neg_pi_div_two_le_of_le
    have h5 : -π / 2 ≤ x / 2 := by
      linarith [h1]
    have h6 : x / 2 ≤ π / 2 := by
      linarith [h2]
    all_goals linarith
  have h6 : 2 + 2 * cos x ≥ 0 := by
    have h7 : cos x ≥ -1 := by
      linarith [neg_one_le_cos x, cos_le_one x]
    linarith
  have h7 : (2 * cos (x / 2)) ^ 2 = 2 + 2 * cos x := by
    have h9 : cos x = 2 * cos (x / 2) ^ 2 - 1 := by
      have h10 : cos x = cos (2 * (x / 2)) := by
        ring_nf
      rw [h10]
      rw [Real.cos_two_mul]
    nlinarith [h9, Real.cos_sq_add_sin_sq (x / 2), Real.cos_sq_add_sin_sq x]
  have h9 : 2 * cos (x / 2) ≥ 0 := by
    nlinarith [h3]
  rw [Real.sqrt_eq_iff_sq_eq] <;> (nlinarith [h9, h6, h7])

theorem algebra_117821 {a : ℕ → ℝ} (ha : ∀ n, a n = sqrt (2 + a (n - 1))) (ha0 : a 0 = 0) :
    ∀ n, a n = 2 * cos (π / 2 ^ (n + 1)) := by
  intro n
  induction n with
  | zero =>
    rw [ha0]
    have h10 : 2 * cos (π / 2 ^ (0 + 1)) = 0 := by
      have h11 : π / 2 ^ (0 + 1) = π / 2 := by norm_num
      rw [h11]
      have h12 : cos (π / 2) = 0 := Real.cos_pi_div_two
      rw [h12]
      all_goals norm_num
    linarith
  | succ n ih =>
    have h10 : a (n + 1) = sqrt (2 + a n) := by
      specialize ha (n + 1)
      simpa using ha
    rw [h10, ih]
    have h11 : 2 * cos (π / 2 ^ (n + 1 + 1)) = 2 * cos ((π / 2 ^ (n + 1)) / 2) := by
      ring_nf
    rw [h11]
    have hx1 : (π / 2 ^ (n + 1) : ℝ) ∈ Icc (-π) π := by
      constructor
      · -- Show that -π ≤ π / 2 ^ (n + 1)
        have h140 : (0 : ℝ) ≤ π / 2 ^ (n + 1) := by positivity
        have h141 : (0 : ℝ) ≥ -π := by 
          linarith [show π > 0 by positivity]
        linarith
      · -- Show that π / 2 ^ (n + 1) ≤ π
        have h190 : (π / 2 ^ (n + 1) : ℝ) ≤ π := by
          have h110 : (2 ^ (n + 1) : ℝ) ≥ 1 := by
            have h175 : 2 ^ (n + 1) ≥ 1 := by
              have h176 : 2 ^ (0 : ℕ) = 1 := by norm_num
              have h177 : ∀ (m : ℕ), 2 ^ (m + 1) ≥ 1 := by
                intro m
                induction m with
                | zero => norm_num
                | succ m ih =>
                  simp [pow_add, pow_mul] at ih ⊢
                  all_goals linarith
              specialize h177 n
              simpa using h177
            exact_mod_cast h175
          have h117 : (π / 2 ^ (n + 1) : ℝ) ≤ π := by
            apply (div_le_iff₀ (by positivity)).mpr
            nlinarith [show π ≥ 0 by positivity]
          linarith
        linarith
    have h12 : sqrt (2 + 2 * cos (π / 2 ^ (n + 1))) = 2 * cos ((π / 2 ^ (n + 1)) / 2) := by
      apply lemma_1
      exact hx1
    simpa using h12