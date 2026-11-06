import Mathlib

theorem algebra_282802 (a b p q t : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) (hpq : p < q) :
    {(AB, v₁, v₂) : ℝ × ℝ × ℝ | 
      v₁ = v₂ + a ∧ 
      AB = v₁ * t ∧ 
      v₂ * t = p / q * AB + b} =
    {((a * t + b) / (1 - p / q), q * (a * t + b) / (t * (q - p)), (a * p * t + b * q) / (t * (q - p)))} := by
  ext ⟨AB, v₁, v₂⟩
  simp [-one_div]
  constructor
  · -- Forward direction: If (AB, v₁, v₂) satisfies the conditions, then it's equal to the singleton set element.
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : v₁ = v₂ + a := by linarith
    have h5 : AB = v₁ * t := by linarith
    have h6 : v₂ * t = p / q * AB + b := by linarith
    have h7 : q - p ≠ 0 := by nlinarith
    have h8 : AB = (a * t + b) / (1 - p / q) := by
      have eq1 : AB * (1 - p / q) = a * t + b := by
        have eq3 : AB = (v₂ + a) * t := by
          have eq4 : v₁ = v₂ + a := h4
          have eq5 : AB = v₁ * t := by linarith
          rw [eq4] at eq5
          linarith
        have eq6 : v₂ * t = p / q * AB + b := h₃
        have eq8 : AB = (v₂ * t) + a * t := by
          nlinarith
        nlinarith [h₃, eq8]
      have eq3 : 1 - p / q ≠ 0 := by
        have h9 : p / q < 1 := by
          apply (div_lt_iff₀ (by linarith)).mpr
          nlinarith
        have h10 : 1 - p / q > 0 := by linarith
        linarith
      field_simp [(show 1 - p / q ≠ 0 by assumption)] at eq1 ⊢
      nlinarith
    have h9 : v₂ = (a * p * t + b * q) / (t * (q - p)) := by
      have h11 : v₂ * t * (q - p) = a * p * t + b * q := by
        have eq2 : v₂ * t = p / q * AB + b := h₃
        rw [h8] at eq2
        field_simp [(show q ≠ 0 by linarith), (show q - p ≠ 0 by nlinarith), (show 1 - p / q ≠ 0 by
          have h9 : p / q < 1 := by
            apply (div_lt_iff₀ (by linarith)).mpr
            nlinarith
          have h10 : 1 - p / q > 0 := by linarith
          linarith
        )] at eq2 ⊢
        nlinarith [mul_pos ht (show 0 < q by linarith), mul_pos hp (show 0 < t by linarith)]
      have h12 : t ≠ 0 := by linarith
      have h13 : q - p ≠ 0 := by nlinarith
      field_simp [(show t ≠ 0 by linarith), (show q - p ≠ 0 by nlinarith)] at h11 ⊢
      nlinarith
    have h10 : v₁ = q * (a * t + b) / (t * (q - p)) := by
      have h11 : v₁ = v₂ + a := h4
      rw [h9] at h11
      field_simp [(show t ≠ 0 by linarith), (show q - p ≠ 0 by nlinarith)] at h11 ⊢
      nlinarith [mul_pos ht (show 0 < q by linarith)]
    simp [h8, h10, h9]
  · -- Backward direction: If (AB, v₁, v₂) is equal to the given expressions, then they satisfy the conditions.
    rintro ⟨rfl, rfl, rfl⟩
    have h7 : q - p ≠ 0 := by
      nlinarith
    constructor
    · -- Show v₁ = v₂ + a
      field_simp [(show t ≠ 0 by linarith), (show q - p ≠ 0 by nlinarith), (show q ≠ 0 by linarith)]
      ring
    constructor
    · -- Show AB = v₁ * t
      field_simp [(show t ≠ 0 by linarith), (show q - p ≠ 0 by nlinarith), (show q ≠ 0 by linarith)]
      all_goals nlinarith
    · -- Show v₂ * t = p / q * AB + b
      field_simp [(show t ≠ 0 by linarith), (show q - p ≠ 0 by nlinarith), (show q ≠ 0 by linarith)]
      all_goals nlinarith