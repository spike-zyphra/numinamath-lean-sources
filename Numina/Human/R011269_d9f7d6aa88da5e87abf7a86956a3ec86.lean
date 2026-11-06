import Mathlib

/-For all real numbers $x, y, z$, prove that:

\[
\left( (x-y)^2 + (x-z)^2 + (y-z)^2 \right)^3 \ge 54 \left[ (x-y)(x-z)(y-z) \right]^2
\]

Determine the conditions under which equality holds.-/
theorem inequalities_613886 (x y z : ℝ) : ((x - y)^2 + (x - z)^2 + (y - z)^2)^3 ≥ 54*((x - y)*(x - z)*(y - z))^2 ∧ (((x - y)^2 + (x - z)^2 + (y - z)^2)^3 = 54*((x - y)*(x - z)*(y - z))^2 ↔ ((x - y = y - z) ∨ x - y = -2 * (y - z) ∨ -2 * (x - y) = y - z))  := by
  constructor
  · wlog hxy : y ≤ x generalizing y x with h₁
    · push_neg at hxy
      specialize h₁ y x hxy.le
      bound
    wlog hxz : z ≤ x generalizing z x with h₂
    · push_neg at hxz
      specialize h₂ x z (by linarith) hxz.le
      bound
    wlog hyz : z ≤ y generalizing z y with h₃
    · push_neg at hyz
      specialize h₃ z y (by linarith) (by linarith) hyz.le
      bound
    set a := x - y with ha₁
    set b := y - z with hb₁
    rw [show x - z = a + b by linarith]
    have ha : 0 ≤ a := by linarith
    have hb : 0 ≤ b := by linarith
    nlinarith [sq_nonneg (a ^ 2 - a * b), sq_nonneg (b ^ 2 - a * b), mul_nonneg ha hb]
  · obtain ⟨a, ha₁⟩ := show ∃ a : ℝ, a = x - y by simp
    obtain ⟨b, hb₁⟩ := show ∃ b : ℝ, b = y - z by simp
    rw [←ha₁, ←hb₁, show x - z = a + b by linarith]
    constructor
    · intro hxy
      rw [show a ^ 2 + (a + b) ^ 2 + b ^ 2 = 2 * (a^2 + a * b + b^2) by ring] at hxy
      by_cases ha₂ : a = 0
      · rw [ha₂] at hxy ⊢
        ring_nf at hxy
        simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, or_false] at hxy
        simp [hxy]
      obtain ⟨t, ht₁⟩ := show ∃ k, k = b / a by simp
      have ht₂ : b = a * t := by rw [ht₁, mul_div_cancel₀ _ ha₂]
      have : (2 * (a ^ 2 + a * b + b ^ 2)) ^ 3 = a^6 * (2 * (1 + t + t^2))^3 := by
        rw [ht₂]
        ring_nf
      rw [this] at hxy
      have : 54 * (a * (a + b) * b) ^ 2 = a^6 * (54 * t^2 * (1 + t) ^ 2) := by
        rw [ht₂]
        ring_nf
      rw [this] at hxy
      simp only [mul_eq_mul_left_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, ha₂, or_false] at hxy
      have ht₃ : (t - 1)^2 * (t + 2)^2 * (2 * t + 1)^2 = 0 := by linarith
      simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, or_assoc] at ht₃
      obtain (ht₃ | ht₃ | ht₃) := ht₃
      · -- t - 1 = 0
        rw [show t = 1 by linarith, Eq.comm, div_eq_one_iff_eq ha₂] at ht₁
        simp [ht₁]
      · -- t + 2 = 0
        rw [show t = -2 by linarith, Eq.comm, div_eq_iff_mul_eq ha₂] at ht₁
        simp [ht₁]
      · -- 2 * t + 1 = 0
        rw [show t = -1 / 2 by linarith, Eq.comm, div_eq_iff_mul_eq ha₂] at ht₁
        simp only [←ht₁]
        ring_nf
        simp
    · rintro (h | h | h)
      · rw [h]
        ring_nf
      · rw [h]
        ring_nf
      · rw [←h]
        ring_nf
