import Mathlib

theorem inequalities_601454 (a b c : ℝ) (h₀ : a + b > c) (h₁ : a + c > b) (h₂ : b + c > a) :
    (2 / 3) * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ∧
    ((2 / 3) * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) = a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ↔ a = b ∧ b = c) := by
  constructor
  · -- First part: inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg ((a + b - c) / 2), sq_nonneg ((a + c - b) / 2), sq_nonneg ((b + c - a) / 2),
      mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁),
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
      mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₀),
      sq_nonneg (3 * a - b - c), sq_nonneg (3 * b - a - c), sq_nonneg (3 * c - a - b),
      mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁), mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), 
      mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₀)]

  · -- Second part: equality
    constructor
    · -- Forward: equality implies a = b ∧ b = c
      intro h_eq
      have h3 : (a - b) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁), mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
          mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₀),
          sq_nonneg ((a + b - c) / 2), sq_nonneg ((a + c - b) / 2), sq_nonneg ((b + c - a) / 2),
          sq_nonneg (3 * a - b - c), sq_nonneg (3 * b - a - c), sq_nonneg (3 * c - a - b)]
      have h4 : a - b = 0 := by 
        rw [sq_eq_zero_iff] at h3 
        exact h3 
      have h5 : (b - c) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁), mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
          mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₀),
          sq_nonneg ((a + b - c) / 2), sq_nonneg ((a + c - b) / 2), sq_nonneg ((b + c - a) / 2),
          sq_nonneg (3 * a - b - c), sq_nonneg (3 * b - a - c), sq_nonneg (3 * c - a - b)]
      have h6 : b - c = 0 := by 
        rw [sq_eq_zero_iff] at h5 
        exact h5 
      have h11 : a = b := by linarith 
      have h22 : b = c := by linarith 
      exact ⟨h11, h22⟩ 
    · -- Backward: a = b ∧ b = c implies equality
      rintro ⟨rfl, rfl⟩ 
      nlinarith [sq_nonneg (1 : ℝ), sq_nonneg (2 * (1 : ℝ) + 1 : ℝ), 
          mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 3 by norm_num)]
      <;> linarith 
      <;> try { simp_all }
      <;> try { nlinarith }
      <;> try { linarith }