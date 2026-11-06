import Mathlib

theorem algebra_238345 {a b c : ℤ} (h : c = (a + b * Complex.I)^3 - 7 * Complex.I) :
    (a = 4 ∧ b = -7 ∧ c = -524) ∨ (a = -4 ∧ b = -7 ∧ c = 524) := by
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [pow_three, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, 
        Complex.sub_re, Complex.sub_im] at eq1 eq2
  have h1 : c = a^3 - 3 * a * b^2 := by
    have h1 : (c : ℂ) = (a^3 - 3 * a * b^2 : ℂ) := by
      ring_nf at eq1 ⊢
      <;> norm_cast at eq1 ⊢
      <;> nlinarith
      all_goals ring_nf <;> norm_num
    norm_cast at h1 ⊢
    all_goals nlinarith
  have h2 : 3 * a^2 * b - b^3 - 7 = 0 := by
    have h2 : (3 * a^2 * b - b^3 - 7 : ℤ) = 0 := by
      have eq2' : (0 : ℂ) = ((3 * (a : ℤ)^2 * (b : ℤ) - (b : ℤ)^3 - 7 : ℤ) : ℂ) := by
        ring_nf at eq2 ⊢
        <;> norm_cast at eq2 ⊢
        <;> nlinarith
      have h3 : ((3 * (a : ℤ)^2 * (b : ℤ) - (b : ℤ)^3 - 7 : ℤ) : ℂ) = (0 : ℂ) := by
        rw [eq2']
        all_goals norm_num [Complex.ext_iff]
      have h4 : (3 * (a : ℤ)^2 * (b : ℤ) - (b : ℤ)^3 - 7 : ℤ) = (0 : ℤ) := by
        norm_cast at h3 ⊢
        all_goals nlinarith
      exact h4
    linarith
  have h5 : b * (3 * a^2 - b^2) = 7 := by 
    nlinarith
  have h6 : b ∣ 7 := by
    use (3 * a^2 - b^2)
    all_goals linarith 
  have h7 : b = 1 ∨ b = -1 ∨ b = 7 ∨ b = -7 := by
    have h8 : b ∣ 7 := h6
    have h9 : b ≤ 7 := by
      exact Int.le_of_dvd (by norm_num) h8
    have h10 : b ≥ -7 := by
      have h11 : (-b : ℤ) ∣ 7 := by
        exact Int.neg_dvd.2 h8
      have h12 : (-b : ℤ) ≤ 7 := by
        exact Int.le_of_dvd (by norm_num) h11
      linarith
    interval_cases b <;> tauto
  rcases h7 with (hb1 | hb2 | hb3 | hb4)
  · -- b = 1
    rw [hb1] at h5
    have h8 : 3 * a^2 = 8 := by
      nlinarith
    exfalso
    have h9 : a^2 ≤ 2 := by
      nlinarith [sq_nonneg (a : ℤ)]
    have h10 : a ≤ 1 := by
      nlinarith [sq_nonneg (a : ℤ)]
    have h11 : a ≥ -1 := by
      nlinarith [sq_nonneg (a : ℤ)]
    interval_cases a <;> omega
  · -- b = -1
    rw [hb2] at h5
    ring_nf at h5
    exfalso
    have h6 : a^2 ≤ 2 := by
      nlinarith [sq_nonneg (a : ℤ)]
    have h7 : a ≤ 1 := by
      nlinarith [sq_nonneg (a : ℤ)]
    have h8 : a ≥ -1 := by
      nlinarith [sq_nonneg (a : ℤ)]
    interval_cases a <;> omega
  · -- b = 7
    rw [hb3] at h5
    ring_nf at h5
    have h11 : a ^ 2 * (21 : ℤ) = 350 := by
      nlinarith
    exfalso
    have h12 : a ^ 2 * (21 : ℤ) % 21 = 0 := by
      omega
    have h13 : a ^ 2 * (21 : ℤ) % 21 = 350 % 21 := by
      omega
    have h14 : (350 : ℤ) % (21 : ℤ) = 2 := by
      omega
    rw [h14] at h13
    omega
  · -- b = -7
    rw [hb4] at h5
    ring_nf at h5
    have h12 : a^2 = 16 := by
      nlinarith
    have h13 : a = 4 ∨ a = -4 := by 
      have h14 : a^2 = 16 := h12
      have : a = 4 ∨ a = -4 := by
        have h15 : a^2 - 16 = 0 := by
          nlinarith
        have h16 : (a - 4) * (a + 4) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h16) with h17 h18
        · -- a - 4 = 0
          left
          linarith
        · -- a + 4 = 0
          right
          nlinarith
      assumption
    cases h13 with
    | inl ha4 => 
      have hc1 : c = -524 := by
        rw [ha4, show b = -7 by linarith] at h1
        nlinarith
      left
      exact ⟨by linarith, by linarith, by linarith⟩
    | inr ha4 => 
      have hc1 : c = 524 := by
        rw [ha4, show b = -7 by linarith] at h1
        nlinarith
      right
      exact ⟨by linarith, by linarith, by linarith⟩