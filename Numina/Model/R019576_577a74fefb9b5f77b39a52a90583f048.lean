import Mathlib

theorem inequalities_599802 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (lambda mu v : ℝ) (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) (hv : 0 ≤ v) (hzw : ¬(lambda = 0 ∧ mu = 0 ∧ v = 0)) :
    a^2 / (lambda * a + mu * b + v * c) + b^2 / (lambda * b + mu * c + v * a) +
    c^2 / (lambda * c + mu * a + v * b) ≥ (a + b + c) / (lambda + mu + v) := by
  have h1 : lambda * a + mu * b + v * c > 0 := by
    by_cases h' : lambda > 0
    · -- If $\lambda > 0$, then $\lambda a + \mu b + v c > 0$ since $a > 0$ and $\mu b + v c \geq 0$
      nlinarith [h', ha, hb, hc, hmu, hv] 
    · -- If $\lambda = 0$
      have h11 : lambda = 0 := by linarith 
      rw [h11] 
      by_cases h₁ : mu > 0
      · -- If $\mu > 0$, then $\mu b + v c > 0$ since $b > 0$ and $v c \geq 0$
        nlinarith [h₁, hb, hc, hlambda, hv] 
      · -- If $\mu = 0$
        have h22 : mu = 0 := by linarith 
        rw [h22] 
        by_cases h₂ : v > 0
        · -- If $v > 0$, then $v c > 0$ since $c > 0$
          nlinarith [h₂, hc, hlambda, hmu, hv] 
        · -- If $v = 0$
          have h33 : v = 0 := by linarith 
          rw [h33] 
          exfalso 
          have h44 : lambda = 0 ∧ mu = 0 ∧ v = 0 := ⟨h11, h22, h33⟩ 
          contradiction 
  have h2 : lambda * b + mu * c + v * a > 0 := by
    by_cases h' : lambda > 0
    · -- If $\lambda > 0$, then $\lambda b + \mu c + v a > 0$ since $b > 0$ and $\mu c + v a \geq 0$
      nlinarith [h', ha, hb, hc, hmu, hv] 
    · -- If $\lambda = 0$
      have h11 : lambda = 0 := by linarith 
      rw [h11] 
      by_cases h₁ : mu > 0
      · -- If $\mu > 0$, then $\mu c + v a > 0$ since $c > 0$ and $v a \geq 0$
        nlinarith [h₁, ha, hb, hc, hlambda, hv] 
      · -- If $\mu = 0$
        have h22 : mu = 0 := by linarith 
        rw [h22] 
        by_cases h₂ : v > 0
        · -- If $v > 0$, then $v a > 0$ since $a > 0$
          nlinarith [h₂, ha, hb, hc, hlambda, hmu, hv] 
        · -- If $v = 0$
          have h33 : v = 0 := by linarith 
          rw [h33] 
          exfalso 
          have h44 : lambda = 0 ∧ mu = 0 ∧ v = 0 := ⟨h11, h22, h33⟩ 
          contradiction 
  have h3 : lambda * c + mu * a + v * b > 0 := by
    by_cases h' : lambda > 0
    · -- If $\lambda > 0$, then $\lambda c + \mu a + v b > 0$ since $c > 0$ and $\mu a + v b \geq 0$
      nlinarith [h', ha, hb, hc, hmu, hv] 
    · -- If $\lambda = 0$
      have h11 : lambda = 0 := by linarith 
      rw [h11] 
      by_cases h₁ : mu > 0
      · -- If $\mu > 0$, then $\mu a + v b > 0$ since $a > 0$ and $v b \geq 0$
        nlinarith [h₁, ha, hb, hc, hlambda, hv] 
      · -- If $\mu = 0$
        have h22 : mu = 0 := by linarith 
        rw [h22] 
        by_cases h₂ : v > 0
        · -- If $v > 0$, then $v b > 0$ since $b > 0$
          nlinarith [h₂, ha, hb, hc, hlambda, hmu, hv] 
        · -- If $v = 0$
          have h33 : v = 0 := by linarith 
          rw [h33] 
          exfalso 
          have h44 : lambda = 0 ∧ mu = 0 ∧ v = 0 := ⟨h11, h22, h33⟩ 
          contradiction 
  have h4 : lambda + mu + v > 0 := by 
    by_contra h
    push_neg at h 
    have h1 : lambda = 0 := by linarith 
    have h2 : mu = 0 := by linarith 
    have h3 : v = 0 := by linarith 
    have h4 : lambda = 0 ∧ mu = 0 ∧ v = 0 := ⟨h1, h2, h3⟩ 
    contradiction 
  have h5 : a^2 / (lambda * a + mu * b + v * c) + b^2 / (lambda * b + mu * c + v * a) + c^2 / (lambda * c + mu * a + v * b) - (a + b + c) / (lambda + mu + v) ≥ 0 := by

    have h6 : a^2 / (lambda * a + mu * b + v * c) + b^2 / (lambda * b + mu * c + v * a) + c^2 / (lambda * c + mu * a + v * b) - (a + b + c) / (lambda + mu + v) =
      ( (a^2 * (lambda * b + mu * c + v * a) * (lambda * c + mu * a + v * b) * (lambda + mu + v) +
          b^2 * (lambda * a + mu * b + v * c) * (lambda * c + mu * a + v * b) * (lambda + mu + v) +
          c^2 * (lambda * a + mu * b + v * c) * (lambda * b + mu * c + v * a) * (lambda + mu + v) -
          (a + b + c) * (lambda * a + mu * b + v * c) * (lambda * b + mu * c + v * a) * (lambda * c + mu * a + v * b) )
          / ( (lambda * a + mu * b + v * c) * (lambda * b + mu * c + v * a) * (lambda * c + mu * a + v * b) * (lambda + mu + v) ) ) := by
      field_simp [h1, h2, h3, h4]
      ring
    rw [h6]
    have h7 : (a^2 * (lambda * b + mu * c + v * a) * (lambda * c + mu * a + v * b) * (lambda + mu + v) +
          b^2 * (lambda * a + mu * b + v * c) * (lambda * c + mu * a + v * b) * (lambda + mu + v) +
          c^2 * (lambda * a + mu * b + v * c) * (lambda * b + mu * c + v * a) * (lambda + mu + v) -
          (a + b + c) * (lambda * a + mu * b + v * c) * (lambda * b + mu * c + v * a) * (lambda * c + mu * a + v * b) ) ≥ 0 := by
      nlinarith [sq_nonneg (a * (lambda * b + mu * c + v * a) - b * (lambda * a + mu * b + v * c)), 
          sq_nonneg (b * (lambda * c + mu * a + v * b) - c * (lambda * b + mu * c + v * a)), 
          sq_nonneg (c * (lambda * a + mu * b + v * c) - a * (lambda * c + mu * a + v * b)), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (lambda * a - mu * b - v * c), 
          sq_nonneg (lambda * b - mu * c - v * a), 
          sq_nonneg (lambda * c - mu * a - v * b), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_nonneg hlambda hmu, mul_nonneg hlambda hv, mul_nonneg hmu hv
          ]
    have h8 : (lambda * a + mu * b + v * c) * (lambda * b + mu * c + v * a) * (lambda * c + mu * a + v * b) * (lambda + mu + v) > 0 := by 
      positivity
    apply div_nonneg 
    linarith 
    all_goals positivity 
  linarith [h5] 
  all_goals 
    linarith