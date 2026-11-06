import Mathlib

theorem number_theory_230141 :
    {(a, b) : ℤ × ℤ | a ≠ b ∧ IsCoprime a b ∧ (a^2 - b^2) * 1801 = 49 * (a^3 - b^3)} = 
    {(25, 24), (24, 25)} := by
  ext ⟨a, b⟩
  simp [-one_div]
  constructor
  · -- Forward direction: prove that equations satisfy values
    rintro ⟨hne, h_coprime, heq⟩
    have h1 : a - b ≠ 0 := by
      intro h
      apply hne
      linarith
    -- Equation (a^2-b^2)*1801 = 49*(a^3-b^3)
    have h2 : (a ^ 2 - b ^ 2) * 1801 = 49 * (a^3 - b^3) := heq
    have h3 : (a - b) * (a + b) * 1801 = 49 * (a - b) * (a ^ 2 + a * b + b ^ 2) := by
      nlinarith
    -- a - b ≠ 0
    have h4 : (a - b : ℤ) ≠ 0 := by
      exact h1
    -- From cross-multiplication
    -- From what was algebraically:
    -- a^2 + a * b + b^2 = 49*(a^2-b^2)/ (a * 2)
    -- Equate to explicit values.
    -- Equation rewriting by cancelling.
    have h5 : 1801 * (a + b) = 49 * (a ^ 2 + a * b + b ^ 2) := by
      apply (mul_left_inj' h4).mp
      linarith
    have h6 : (49 : ℤ) ∣ 1801 * (a + b) := by
      use (a ^ 2 + a * b + b ^ 2)
      all_goals
        try { nlinarith } <;> try { linarith }
    have h7 : (49 : ℤ) ∣ (a + b) := by
      have h2' : (49 : ℤ) ∣ 1801 * (a + b) := h6
      have h3' : IsCoprime (49 : ℤ) (1801 : ℤ) := by
        norm_num [Int.isCoprime_iff_gcd_eq_one]
      -- IsCoprime used here.
      have h4' : (49 : ℤ) ∣ (a + b) := by
        apply IsCoprime.dvd_of_dvd_mul_left h3' h2'
      exact h4'
    obtain ⟨k, hk⟩ := h7
    have h8 : a + b = 49 * k := by 
      linarith
    have h9 : 1801 * k = a ^ 2 + a * b + b ^ 2 := by
      nlinarith [h5, h8]
    have h9' : k ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 49 * k), sq_nonneg (a), sq_nonneg (b), h_coprime]
    have h10 : k ≤ 1 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 49 * k), sq_nonneg (a - 24), sq_nonneg (a - 25), sq_nonneg (b - 24), sq_nonneg (b - 25), h_coprime]
    have h11 : k = 0 ∨ k = 1 := by 
      omega
    cases h11 with
    | inl h11 =>
      -- k = 0
      have h12 : k = 0 := h11
      have h13 : a + b = 0 := by
        rw [h12] at hk
        nlinarith
      have h14 : a ^ 2 + a * b + b ^ 2 = 0 := by
        rw [h12] at h9
        linarith
      have h15 : a * b ≥ 0 := by
        nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), h14]
      have h16 : a = 0 := by
        nlinarith [sq_nonneg (a), sq_nonneg (b), h14, h15, h13, h_coprime]
      have h17 : b = 0 := by
        nlinarith [sq_nonneg (a), sq_nonneg (b), h14, h15, h13, h_coprime]
      exfalso
      exact hne (by
        linarith)
    | inr h11 =>
      -- k = 1
      have h12 : k = 1 := h11
      have h13 : a + b = 49 := by
        rw [h12] at hk
        nlinarith
      have h14 : a ^ 2 + a * b + b ^ 2 = 1801 := by
        rw [h12] at h9
        nlinarith 
      have h15 : (a - b) ^ 2 = 1 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 49), sq_nonneg (a - 24), sq_nonneg (a - 25), sq_nonneg (b - 24), sq_nonneg (b - 25), h_coprime, h13, h14]
      have h16 : (a - b) = 1 ∨ (a - b) = -1 := by
        rw [sq_eq_one_iff] at h15
        tauto
      cases h16 with
      | inl h17 =>
        -- a - b = 1
        have h17' : a - b = 1 := h17
        have h18 : b = a - 1 := by linarith
        rw [show b = a - 1 by linarith [h18]] at h13 h14
        have h19 : a = 25 := by
          nlinarith [sq_nonneg (a - 25), sq_nonneg (a - 24)]
        have h20 : b = 24 := by
          linarith [h19, h18]
        simp [h19, h20]
      | inr h18 =>
        -- a - b = -1
        have h18' : a - b = -1 := h18
        have h19 : a = b - 1 := by linarith
        rw [show a = b - 1 by linarith [h19]] at h13 h14
        have h20 : b = 25 := by
          nlinarith [sq_nonneg (b - 25), sq_nonneg (b - 24)]
        have h21 : a = 24 := by
          linarith [h20, h19]
        simp [h21, h20]
  · -- Backward direction: show the solutions satisfy all conditions
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · norm_num 
      constructor 
      · norm_num [Int.isCoprime_iff_gcd_eq_one]
      · norm_num
    · constructor
      · norm_num 
      constructor 
      · norm_num [Int.isCoprime_iff_gcd_eq_one]
      · norm_num