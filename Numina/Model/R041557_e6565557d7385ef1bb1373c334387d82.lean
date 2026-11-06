import Mathlib

theorem inequalities_133965 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    1 / 2 ≤ a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) ∧
    (1 / 2 = a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) ↔
      (a = b ∧ b = c ∧ c = d))
  := by
  have h1 : a ^ 2 / (a + b) ≥ (3 * a - b) / 4 := by
    have h11 : 0 < a + b := by linarith
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (a - b)]
  
  have h2 : b ^ 2 / (b + c) ≥ (3 * b - c) / 4 := by
    have h11 : 0 < b + c := by linarith
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (b - c)]
  
  have h3 : c ^ 2 / (c + d) ≥ (3 * c - d) / 4 := by
    have h11 : 0 < c + d := by linarith
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (c - d)]
  
  have h4 : d ^ 2 / (d + a) ≥ (3 * d - a) / 4 := by
    have h11 : 0 < d + a := by linarith
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (d - a)]
  
  constructor
  · -- Proof that 1/2 ≤ ...
    have h5 : a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) ≥ 1 / 2 := by
      linarith
    linarith
  · -- Proof that 1/2 = ... ↔ (a = b ∧ b = c ∧ c = d)
    constructor
    · -- Proof of →
      intro heq
      have heq1 : a ^ 2 / (a + b) = (3 * a - b) / 4 := by
        linarith
      have heq2 : b ^ 2 / (b + c) = (3 * b - c) / 4 := by
        linarith
      have heq3 : c ^ 2 / (c + d) = (3 * c - d) / 4 := by
        linarith
      have heq4 : d ^ 2 / (d + a) = (3 * d - a) / 4 := by
        linarith
      have heq5 : (a - b) ^ 2 = 0 := by
        have h11 : 0 < a + b := by linarith
        have h12 : a ^ 2 = (3 * a - b) * (a + b) / 4 := by
          have h13 : a ^ 2 / (a + b) = (3 * a - b) / 4 := heq1
          field_simp [(show a + b ≠ 0 by positivity)] at h13 ⊢
          nlinarith
        nlinarith
      have heq6 : a - b = 0 := by
        nlinarith
      have heq7 : (b - c) ^ 2 = 0 := by
        have h11 : 0 < b + c := by linarith
        have h12 : b ^ 2 = (3 * b - c) * (b + c) / 4 := by
          have h13 : b ^ 2 / (b + c) = (3 * b - c) / 4 := heq2
          field_simp [(show b + c ≠ 0 by positivity)] at h13 ⊢
          nlinarith
        nlinarith
      have heq8 : b - c = 0 := by
        nlinarith
      have heq9 : (c - d) ^ 2 = 0 := by
        have h11 : 0 < c + d := by linarith
        have h12 : c ^ 2 = (3 * c - d) * (c + d) / 4 := by
          have h13 : c ^ 2 / (c + d) = (3 * c - d) / 4 := heq3
          field_simp [(show c + d ≠ 0 by positivity)] at h13 ⊢
          nlinarith
        nlinarith
      have heq10 : c - d = 0 := by
        nlinarith
      constructor
      · linarith
      constructor
      · linarith
      · linarith
    · -- Proof of ←
      rintro ⟨r1, r2, r3⟩
      have ha1 : a = b := r1
      have hb1 : b = c := r2
      have hc1 : c = d := r3
      have ha2 : b = a := by linarith
      have ha3 : c = a := by linarith
      have ha4 : d = a := by linarith
      rw [show b = a by linarith, show c = a by linarith, show d = a by linarith]
      field_simp [(show a + a ≠ 0 by positivity)]
      nlinarith