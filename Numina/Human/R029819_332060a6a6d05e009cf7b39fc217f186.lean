import Mathlib

open Real Set
open scoped Real

/-Find the maximum value of
\[\sin \frac{\theta}{2} \cdot (1 + \cos \theta)\]for $0 < \theta < \pi.$-/
theorem calculus_16425 :
  IsGreatest {x | ∃ θ : ℝ, θ ∈ Ioo 0 Real.pi ∧ x = sin (θ / 2) * (1 + cos θ)} (4 * sqrt 3 / 9) := by
  unfold IsGreatest
  -- ∀x, (1 + cos x) = 2 * cos^2 (x / 2) = 2 * (1 - sin^2 (x / 2))
  have eq: ∀ x : ℝ, (1 + cos x) = 2 * (1 - (sin (x / 2)) ^ 2) := by
    intro x
    rw [sin_sq_eq_half_sub]
    field_simp
    ring_nf
  simp

  constructor
  . -- first, we prove that 4√3/9 is in the set.
    use 2 * arcsin (1/√3)
    constructor
    . field_simp
      apply lt_of_le_of_ne
      linarith [arcsin_le_pi_div_two (1/√3)]
      intro h
      have h: arcsin (1/√3) = π/2 := by linarith
      have : 1/√3 = sin (π/2) := by
        rw [h.symm, sin_arcsin]
        linarith [(by positivity: 0 < 1/√3)]
        have : 1 < √3 := by exact lt_sqrt_of_sq_lt (by linarith)
        refine (one_div_le ?_ ?_).mp ?_
        repeat linarith
      rw [sin_pi_div_two] at this
      absurd this
      refine div_ne_one_of_ne ?_
      apply ne_of_lt
      exact lt_sqrt_of_sq_lt (by linarith)
    . rw [eq]
      field_simp
      rw [sin_arcsin]
      field_simp
      rw [mul_assoc, ←mul_assoc √3, mul_self_sqrt (by positivity)]
      norm_num
      linarith [(by positivity: 0 < 1/√3)]
      have : 1 < √3 := by exact lt_sqrt_of_sq_lt (by linarith)
      refine (one_div_le ?_ ?_).mp ?_
      repeat linarith
  . -- second, we prove that any element in the set is less than 4√3/9.
    apply mem_upperBounds.mpr
    intro y
    simp
    intro θ hθ₁ hθ₂ heq
    rw [eq] at heq
    -- let x = sin(θ/2), we have: y = 2x * (1 - x^2)
    obtain ⟨x, hx₁⟩ := (by simp: ∃x, x = sin (θ/2))
    rw [hx₁.symm] at heq
    ring_nf at heq
    -- Note that:
    have hy: y^2 = 4 * x^2 * (1 - x^2) * (1 - x^2) := by rw [heq]; ring_nf
    -- by AM-GM inequality, we have:
    have hAMGM: 2 * x^2 * (1 - x^2) * (1 - x^2) ≤ 8/27 := by
      have : 8/27 = (((2*x^2) + (1 - x^2) + (1 - x^2))/3)^3 := by ring_nf
      rw [this]
      have ineq {a b : ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b): a^(1/3 : ℝ) ≤ b → a ≤ b^3 := by
        intro hab
        by_cases h0: a = 0
        . rw [h0]
          rw [h0] at hab
          simp at hab
          exact pow_nonneg hb 3
        have ha: 0 < a := by exact lt_of_le_of_ne ha fun a_1 ↦ h0 (id (Eq.symm a_1))
        by_cases h0: b = 0
        . rw [h0] at hab
          linarith [Real.rpow_pos_of_pos ha (1 / 3)]
        have hb: 0 < b := by exact lt_of_le_of_ne hb fun b_1 ↦ h0 (id (Eq.symm b_1))
        rw [Real.rpow_le_iff_le_log (by assumption) (by assumption)] at hab
        apply Real.pow_le_of_le_log hb
        norm_cast at hab
        norm_cast
        linarith

      have geom_mean_le_arith_mean3_weighted' (p₁ p₂ p₃ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) : (p₁ * p₂ * p₃)^(1/3: ℝ) ≤ (1/3: ℝ) * (p₁ + p₂ + p₃) := by
        rw [mul_rpow, mul_rpow, mul_add, mul_add]
        apply geom_mean_le_arith_mean3_weighted
        repeat positivity
        linarith
        repeat positivity
      have : 0 ≤ 1 - x^2 := by
        rw [hx₁]
        linarith [sin_sq_le_one (θ / 2)]
      specialize geom_mean_le_arith_mean3_weighted' (2 * x^2) (1 - x^2) (1 - x^2)
      specialize geom_mean_le_arith_mean3_weighted' (by positivity) this this
      apply ineq ?_ ?_
      rw (config := {occs := .pos [2]} ) [div_eq_mul_inv]
      rw [mul_comm (2 * x ^ 2 + (1 - x ^ 2) + (1 - x ^ 2)), ←one_div]
      exact geom_mean_le_arith_mean3_weighted'
      bound
      bound
    have : 16 / 27 = (4 * √3 / 9)^2 := by
      ring_nf
      rw [sq_sqrt]
      ring_nf
      positivity
    by_cases h': y ≤ 0
    . apply le_trans
      exact h'
      positivity
    exact (pow_le_pow_iff_left (by linarith) (by positivity) (by norm_num: 2 ≠ 0)).mp (by linarith)
