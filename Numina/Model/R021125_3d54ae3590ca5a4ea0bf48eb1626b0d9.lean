import Mathlib

theorem inequalities_91580 (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : 1 / p + 1 / q = 1) :
    1 / 3 ≤ 1 / (p * (p + 1)) + 1 / (q * (q + 1)) ∧
    1 / (p * (p + 1)) + 1 / (q * (q + 1)) < 1 / 2 ∧
    1 ≤ 1 / (p * (p - 1)) + 1 / (q * (q - 1)) := by
  have h1 : p * q = p + q := by
    field_simp at h 
    nlinarith 
  have h2 : 1 / (p * (p + 1)) + 1 / (q * (q + 1)) = 1 - (1 / (p + 1) + 1 / (q + 1)) := by 
    have eq1 : 1 / (p * (p + 1)) = 1 / p - 1 / (p + 1) := by 
      field_simp 
    have eq2 : 1 / (q * (q + 1)) = 1 / q - 1 / (q + 1) := by 
      field_simp 
    rw [eq1, eq2]
    linarith 
  have h3 : 1 / (p + 1) + 1 / (q + 1) = (p * q + 2) / (2 * (p * q) + 1) := by 
    field_simp [(show p + 1 ≠ 0 by linarith), (show q + 1 ≠ 0 by linarith)]
    nlinarith [h1]
  have h4 : 1 / (p * (p + 1)) + 1 / (q * (q + 1)) = (p * q - 1) / (2 * (p * q) + 1) := by 
    rw [h2, h3]
    field_simp 
    <;> nlinarith 
  have h5 : 0 < p * q := by nlinarith 
  have h6 : p * q ≥ 4 := by
    nlinarith [sq_nonneg (p - q), h1, mul_pos hp hq]
  constructor 
  · -- Prove 1 / 3 ≤ 1 / (p * (p + 1)) + 1 / (q * (q + 1))
    rw [h4] 
    apply (le_div_iff₀ (by nlinarith)).mpr 
    nlinarith 
  constructor 
  · -- Prove 1 / (p * (p + 1)) + 1 / (q * (q + 1)) < 1 / 2 
    rw [h4] 
    apply (div_lt_iff₀ (by nlinarith)).mpr 
    nlinarith 
  · -- Prove 1 ≤ 1 / (p * (p - 1)) + 1 / (q * (q - 1))
    have h7 : 1 / (p * (p - 1)) + 1 / (q * (q - 1)) = (1 / (p - 1) - 1 / p) + (1 / (q - 1) - 1 / q) := by
      field_simp [(show p ≠ 0 by linarith), (show p - 1 ≠ 0 by
        by_contra h8 
        have : p = 1 := by linarith 
        rw [this] at h 
        field_simp at h 
      ), (show q ≠ 0 by linarith), (show q - 1 ≠ 0 by
        by_contra h8 
        have : q = 1 := by linarith 
        rw [this] at h 
        field_simp at h 
      )] 
      <;> ring
    have h8 : 1 / (p * (p - 1)) + 1 / (q * (q - 1)) = (1 / (p - 1) + 1 / (q - 1)) - (1 / p + 1 / q) := by
      rw [h7] 
      ring
    have h9 : 1 / p + 1 / q = 1 := h 
    rw [h8, h9] 
    have h10 : 1 / (p - 1) + 1 / (q - 1) = p * q - 2 := by 
      field_simp [(show p - 1 ≠ 0 by 
          by_contra h8 
          have : p = 1 := by linarith 
          rw [this] at h 
          field_simp at h 
        ), (show q - 1 ≠ 0 by 
          by_contra h8 
          have : q = 1 := by linarith 
          rw [this] at h 
          field_simp at h 
        )] 
      nlinarith [h1, sq_nonneg (p - q), sq_nonneg ((p - 1) * (q - 1)), mul_pos hp hq]
    nlinarith [h10, h6]