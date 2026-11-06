import Mathlib

open Real

theorem inequalities_79154 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    sqrt a + 1 > sqrt b ↔ ∀ x > 1, a * x + x / (x - 1) > b := by
  constructor
  · -- Forward direction: (√a + 1 > √b) → (∀ x > 1, a * x + x / (x - 1) > b)
    intro h
    intro x hx
    have h1 : sqrt a + 1 > sqrt b := h
    have h2 : (sqrt a + 1) ^ 2 > b := by
      have h3 : sqrt a + 1 > sqrt b := h
      have h4 : sqrt b ^ 2 = b := by rw [Real.sq_sqrt]; positivity
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    
    have h3 : ∀ x > 1, a * x + x / (x - 1) ≥ (sqrt a + 1) ^ 2 := by
      intro x hx
      have hx' : 0 < x - 1 := by linarith
      have h4 : a * x + x / (x - 1) - (sqrt a + 1) ^ 2 ≥ 0 := by
        have h5 : a * x + x / (x - 1) - (sqrt a + 1) ^ 2 =
            (a * x ^ 2 + (-a + 1) * x - (sqrt a + 1) ^ 2 * (x - 1)) / (x - 1) := by 
          field_simp <;> ring_nf
          <;> field_simp <;> ring_nf
        rw [h5]
        apply div_nonneg
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith),
                  sq_nonneg (x - (1 + 1 / sqrt a)), sq_nonneg (sqrt a * (x - 1) - 1), 
                  sq_nonneg (sqrt a * x - 1), sq_nonneg (sqrt a * (x - 1) - sqrt a),
                  sq_nonneg (sqrt a - 1), sq_nonneg (x - 1),
                  Real.sqrt_nonneg a, sq_nonneg (sqrt a * (x - 1) - 1)]
        linarith [Real.sqrt_nonneg a]
      linarith

    have h4 : a * x + x / (x - 1) > b := by
      have h5 : a * x + x / (x - 1) ≥ (sqrt a + 1) ^ 2 := h3 x hx
      have h6 : (sqrt a + 1) ^ 2 > b := h2
      linarith

    exact h4
  · -- Backward direction: (∀ x > 1, a * x + x / (x - 1) > b) → (√a + 1 > √b)
    intro h
    have h1 := h (1 + 1 / sqrt a) (by
      have h1 : sqrt a > 0 := by positivity
      have h2 : (1 + 1 / sqrt a) > 1 := by 
        have : 1 / sqrt a > 0 := by 
          apply div_pos
          norm_num
          all_goals linarith [Real.sqrt_nonneg a]
        nlinarith
      linarith
    )
    have h5 : (sqrt a + 1) ^ 2 > b := by
      have h5 : a * (1 + 1 / sqrt a) + (1 + 1 / sqrt a) / (1 + 1 / sqrt a - 1) = (sqrt a + 1) ^ 2 := by
        have h5' : sqrt a > 0 := by positivity
        field_simp [h5'.ne.symm]
        <;> ring_nf <;> field_simp [h5'.ne.symm]
        <;> ring_nf
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sqrt_nonneg a]
      have h6 : a * (1 + 1 / sqrt a) + (1 + 1 / sqrt a) / (1 + 1 / sqrt a - 1) > b := h1
      nlinarith [h5]
    
    have h6 : sqrt a + 1 > sqrt b := by
      have h7 : (sqrt a + 1) ^ 2 > b := h5
      have h8 : sqrt b ^ 2 = b := by 
        rw [Real.sq_sqrt]
        positivity
      have h9 : sqrt a + 1 > sqrt b := by
        nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith)]
      exact h9

    exact h6