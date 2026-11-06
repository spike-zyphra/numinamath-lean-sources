import Mathlib

open Real Set

/- 2. Solve the inequality $2 \cdot 5^{2 x} \cdot \sin 2 x-3^{x} \geq 5^{2 x}-2 \cdot 3^{x} \cdot \sin 2 x$. -/
theorem inequalities_107283 (x : ℝ) :
    2 * 5^(2 * x) * sin (2 * x) - 3^x ≥ 5^(2 * x) - 2 * 3^x * sin (2 * x) ↔
    ∃ k : ℤ, (Real.pi / 12 + Real.pi * k ≤ x ∧ x ≤ 5 * Real.pi / 12 + Real.pi * k) := by
  -- first we define θ as arcsin(sin(2x)), this is because properties of sin are well behaving at θ which is inside [-π / 2, π / 2] with same value at sin
  let θ := arcsin (sin (2 * x))
  -- prove sin (x) = sin θ, and bounds theta and relation between θ, x which will be used later
  have h : sin (2 * x) = sin θ := by
    rw [sin_arcsin]
    . apply neg_one_le_sin
    . apply sin_le_one
  have h' := sin_eq_sin_iff.mp h
  have hθ_ub : θ ≤ π / 2 := by apply arcsin_le_pi_div_two
  have hθ_lb : - (π / 2) ≤ θ := by apply neg_pi_div_two_le_arcsin
  calc
    -- first convert lhs to factored form
    _ ↔ 0 ≤ (5 ^ (2 * x) + 3 ^ x) * (sin (2 * x) - 1 / 2) := by
      constructor <;> rintro h <;> linarith
    -- since (5^(2x) + 3^x) is always positive,  we can convert lhs to just inequality of sin
    _ ↔ 0 ≤ (sin (2 * x) - 1 / 2) := by
      rw [mul_nonneg_iff_of_pos_left]
      positivity
    _ ↔ 1/2 ≤ sin (2 * x) := by
      constructor <;> rintro h <;> linarith
    -- write the inequality as sin (π/6) ≤ sin θ, this will allow using monotonicity of sin
    _ ↔ sin (π / 6) ≤ sin θ := by
      rw [← sin_pi_div_six, h]
    _ ↔ π/6 ≤ θ := by
      apply StrictMonoOn.le_iff_le Real.strictMonoOn_sin
      all_goals simp; and_intros
      . linarith [pi_pos]
      . linarith [pi_pos]
      . assumption
      . assumption
    _ ↔ _ := by
      -- now we prove both direction separately
      constructor
      -- if π/6 ≤ θ, then we do casework on the two relations of θ and x
      . rintro hθ
        obtain ⟨k, h'' | h''⟩ := h'
        -- first case θ = 2 * k * π + 2 * x, then we can use -k for target inequality
        . use -k
          push_cast
          and_intros <;> linarith
        -- second case θ = (2 * k + 1) * π - 2 * x, then we can use k for target inequality
        . use k
          and_intros <;> linarith
      -- for opposite direction, extract k' from hypothesis
      . rintro ⟨k', hx_lb, hx_ub⟩
        -- do casework on the two relation between x and θ
        obtain ⟨k, h'' | h''⟩ := h'
        -- first case if θ = 2 * k * π + 2 * x, then we can use the hx_lb, hx_ub, hθ_ub, hθ_lb to squeeze (k+k') between -1, 1, so it is 0, hence k' = -k, then hypothesis implies π/6 ≤ θ
        . have hk1 : π * (k + k') < π * 1 := by linarith [pi_pos]
          replace hk1 : k + k' < 1 := by
            rify
            exact lt_of_mul_lt_mul_left hk1 pi_nonneg
          have hk2 : π * -1 < π * (k + k') := by linarith [pi_pos]
          replace hk2 : -1 < k + k' := by
            rify
            exact lt_of_mul_lt_mul_left hk2 pi_nonneg
          have hk : k' = -k := by omega
          rw [hk] at hx_lb; push_cast at hx_lb
          linarith [pi_pos]
        -- first case if θ = (2 * k + 1) * π - 2 * x, then we can use the hx_lb, hx_ub, hθ_ub, hθ_lb to squeeze (k-k') between -1, 1, so it is 0, hence k' = k, then hypothesis implies π/6 ≤ θ
        . have hk1 : π * (k - k') < π * 1 := by linarith [pi_pos]
          replace hk1 : k - k' < 1 := by
            rify
            exact lt_of_mul_lt_mul_left hk1 pi_nonneg
          have hk2 : π * -1 < π * (k - k') := by linarith [pi_pos]
          replace hk2 : -1 < k - k' := by
            rify
            exact lt_of_mul_lt_mul_left hk2 pi_nonneg
          have hk : k' = k := by omega
          rw [hk] at hx_ub
          linarith [pi_pos]