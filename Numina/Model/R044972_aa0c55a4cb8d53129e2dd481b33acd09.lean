import Mathlib

theorem algebra_156370 {r s t₁ t₂ t₃ v V x : ℝ}
  (vpos : v > 0)
  (Vpos : V > 0)
  (tpos : t₂ > 0)
  (tpos2 : t₂ - t₁ > 0)
  (h₁ : s = v * t₂ + V * (t₂ - t₁))
  (h₂ : s / v = s / V + t₁ - r)
  (h₃ : v * (x - t₃) + V * (x - t₃) = v * t₂ + V * (t₂ - t₁)) :
  v / V = (r + √(r^2 + 4 * t₂ * (t₂ - t₁))) / (2 * t₂) ∧ x = t₃ + t₂ - t₁ / (1 + v/V) := by
  have h4 : s ≠ 0 := by
    nlinarith [h₁, vpos, Vpos, tpos, tpos2]
  have h5 : s * V = s * v + (t₁ - r) * v * V := by
    have h6 : s / v = s / V + t₁ - r := by linarith [h₂]
    have h7 : s * V = s * v + (t₁ - r) * v * V := by
      field_simp [(show v ≠ 0 by linarith), (show V ≠ 0 by linarith)] at h6 ⊢
      nlinarith [h6]
    linarith [h7]
  have h8 : (t₂ - t₁) * V ^ 2 + r * v * V - t₂ * v ^ 2 = 0 := by
    rw [h₁] at h5
    nlinarith [h5]
  have h9 : (v / V) = (r + Real.sqrt (r ^ 2 + 4 * t₂ * (t₂ - t₁))) / (2 * t₂) := by
    have h10 : (t₂ - t₁) * (V / v) ^ 2 + r * (V / v) - t₂ = 0 := by
      have h11 : (t₂ - t₁) * V ^ 2 + r * v * V - t₂ * v ^ 2 = 0 := by linarith [h8]
      have h12 : (t₂ - t₁) * (V / v) ^ 2 + r * (V / v) - t₂ = 0 := by
        have h13 : v ≠ 0 := by linarith
        field_simp at h11 ⊢
        nlinarith
      linarith
    -- Use quadratic formula to solve for V / v
    have h12 : (V / v) = (-r + Real.sqrt (r ^ 2 + 4 * t₂ * (t₂ - t₁))) / (2 * (t₂ - t₁)) := by 
      have h13 : ((t₂ - t₁) * (V / v) + r / 2 + Real.sqrt (r ^ 2 + 4 * t₂ * (t₂ - t₁)) / 2) * ((t₂ - t₁) * (V / v) + r / 2 - Real.sqrt (r ^ 2 + 4 * t₂ * (t₂ - t₁)) / 2) = 0 := by
        nlinarith [h10, Real.sqrt_nonneg (r ^ 2 + 4 * t₂ * (t₂ - t₁)), Real.sq_sqrt (show r ^ 2 + 4 * t₂ * (t₂ - t₁) ≥ 0 by nlinarith)]
      cases' (mul_eq_zero.mp h13) with h14 h15
      · -- Case $\text{first factor} = 0$
        field_simp [(show t₂ - t₁ ≠ 0 by nlinarith [tpos2])] at h14 ⊢
        nlinarith [Real.sqrt_nonneg (r ^ 2 + 4 * t₂ * (t₂ - t₁)), Real.sq_sqrt (show r ^ 2 + 4 * t₂ * (t₂ - t₁) ≥ 0 by nlinarith)]
      · -- Case $\text{second factor} = 0$
        field_simp [(show t₂ - t₁ ≠ 0 by nlinarith [tpos2])] at h15 ⊢
        nlinarith [Real.sqrt_nonneg (r ^ 2 + 4 * t₂ * (t₂ - t₁)), Real.sq_sqrt (show r ^ 2 + 4 * t₂ * (t₂ - t₁) ≥ 0 by nlinarith)]
    -- Then we can compute $v / V$ as $1 / (V / v)$
    have h16 : v ≠ 0 := by linarith
    have h17 : V ≠ 0 := by linarith
    field_simp at h12 ⊢
    nlinarith [Real.sqrt_nonneg (r ^ 2 + 4 * t₂ * (t₂ - t₁)), Real.sq_sqrt (show r ^ 2 + 4 * t₂ * (t₂ - t₁) ≥ 0 by nlinarith)]
  have h14 : x = t₃ + t₂ - t₁ / (1 + v / V) := by
    have h15 : v * (x - t₃) + V * (x - t₃) = v * t₂ + V * (t₂ - t₁) := h₃
    have h16 : (v + V) * (x - t₃) = v * t₂ + V * (t₂ - t₁) := by
      linarith [h15]
    have h17 : x - t₃ = (v * t₂ + V * (t₂ - t₁)) / (v + V) := by
      have h18 : v + V ≠ 0 := by linarith
      field_simp at h16 ⊢
      linarith
    have h18 : x = t₃ + (v * t₂ + V * (t₂ - t₁)) / (v + V) := by
      linarith [h17]
    have h21 : x = t₃ + t₂ - t₁ / (1 + v / V) := by
      rw [h18]
      field_simp [(show v + V ≠ 0 by linarith), (show 1 + v / V ≠ 0 by
        field_simp
        linarith
      )] at *
      <;> nlinarith [Real.sqrt_nonneg (r ^ 2 + 4 * t₂ * (t₂ - t₁)), Real.sq_sqrt (show r ^ 2 + 4 * t₂ * (t₂ - t₁) ≥ 0 by nlinarith)]
    linarith
  constructor
  · -- Proof of the first part
    linarith [h9]
  · -- Proof of the second part
    linarith [h14]