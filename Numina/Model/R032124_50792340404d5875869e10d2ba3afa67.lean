import Mathlib

theorem algebra_122634 (a b c d : ℤ) : 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
    a * b + c * d = a + b + c + d + 3 ↔
    (a, b, c, d) = (1, 1, 2, 6) ∨ (a, b, c, d) = (1, 2, 2, 6) ∨
    (a, b, c, d) = (2, 2, 2, 5) ∨ (a, b, c, d) = (2, 2, 3, 3) := by
  constructor
  · -- Forward: if (a, b, c, d) satisfies the constraints and equation, it's one of the solutions.
    rintro ⟨ha1, hab, hbc, hcd, heq⟩
    have ha2 : a ≤ 2 := by 
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 1 : ℤ), sq_nonneg (c - 1 : ℤ), sq_nonneg (d - 3 : ℤ), 
            sq_nonneg (a - 2 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (c - 2 : ℤ), sq_nonneg (d - 4 : ℤ)]
    have ha1' : a = 1 ∨ a = 2 := by 
      omega
    rcases ha1' with (ha | ha)
    · -- Assume a = 1.
      have h1 : a = 1 := ha
      rw [h1] at heq
      have h2 : b + c * d = b + c + d + 4 := by 
        nlinarith
      have h3 : (c - 1) * (d - 1) = 5 := by
        nlinarith 
      have h4 : (c - 1 : ℤ) = 1 ∨ (c - 1 : ℤ) = 5 ∨ (c - 1 : ℤ) = -1 ∨ (c - 1 : ℤ) = -5 := by 
        have h5 : (c - 1) * (d - 1) = 5 := h3
        have h6 : (c - 1 : ℤ) ∣ 5 := by
          use (d - 1)
          linarith
        have h7 : (c - 1 : ℤ) = 1 ∨ (c - 1 : ℤ) = 5 ∨ (c - 1 : ℤ) = -1 ∨ (c - 1 : ℤ) = -5 := by 
          have h8 : (c - 1 : ℤ) ∣ 5 := h6
          have h10 : (c - 1 : ℤ) ≤ 5 := by
            exact Int.le_of_dvd (by norm_num) h8
          have h11 : (c - 1 : ℤ) ≥ -5 := by
            have h9 : (- (c - 1) : ℤ) ∣ 5 := by
              exact Int.neg_dvd.2 h8
            have h12 : (- (c - 1) : ℤ) ≤ 5 := by
              exact Int.le_of_dvd (by norm_num) h9
            omega
          interval_cases (c - 1 : ℤ) <;> tauto
        assumption
      rcases h4 with (h4 | h4 | h4 | h4)
      · -- Case where c - 1 = 1, so c = 2.
        have hc1 : c = 2 := by 
          linarith
        have hd1 : d = 6 := by
          nlinarith 
        have h8 : b = 1 ∨ b = 2 := by 
          have hb : b ≤ (c : ℤ) := hbc
          have hb2 : (b : ℤ) ≥ 1 := by linarith [hab]
          rw [hc1] at hb 
          have hb3 : b ≤ 2 := by linarith 
          omega 
        rcases h8 with (h8 | h8)
        · -- Case b = 1. Then the quadruple is (1, 1, 2, 6).
          have hb1 : b = 1 := h8 
          simp [Prod.ext_iff, h1, hb1, hc1, hd1]
        · -- Case b = 2. Then the quadruple is (1, 2, 2, 6).
          have hb2 : b = 2 := h8 
          simp [Prod.ext_iff, h1, hb2, hc1, hd1]
      · -- Case where c - 1 = 5, so c = 6.
        have hc2 : c = 6 := by 
          linarith 
        nlinarith 
      · -- Case where c - 1 = -1, so c = 0.
        have hc3 : c = 0 := by 
          linarith 
        nlinarith 
      · -- Case where c - 1 = -5, so c = -4.
        have hc4 : c = -4 := by 
          linarith 
        nlinarith 
    · -- Assume a = 2.
      have h1 : a = 2 := ha 
      rw [h1] at heq 
      -- heq: 2 * b + c * d = 2 + b + c + d + 3
      have h5 : 2 * b + c * d = 2 + b + c + d + 3 := by 
        linarith 
      -- Simplify to b + c * d - c - d = 5
      have h6 : b + c * d - c - d = 5 := by 
        nlinarith 
      have ha2' : c ≥ 2 := by 
        linarith [hbc, ha] 
      have ha3' : c ≤ 6 := by 
        nlinarith [sq_nonneg (c - 3 : ℤ), sq_nonneg (d - 3 : ℤ), sq_nonneg (b - 2 : ℤ)]
      interval_cases c <;> try { 
        omega 
      } <;> try { 
        have : d ≤ 10 := by nlinarith 
        have : d ≥ -1 := by nlinarith 
        interval_cases d <;> norm_num [Prod.ext_iff, h1] at *
        <;> omega 
      }
  · -- Backward: verify solutions satisfy the constraints and equation.
    rintro (h | h | h | h)
    · -- First solution (1, 1, 2, 6).
      simp [Prod.ext_iff] at h 
      rcases h with ⟨rfl, rfl, rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      all_goals norm_num 
    · -- Second solution (1, 2, 2, 6).
      simp [Prod.ext_iff] at h 
      rcases h with ⟨rfl, rfl, rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      all_goals norm_num 
    · -- Third solution (2, 2, 2, 5).
      simp [Prod.ext_iff] at h 
      rcases h with ⟨rfl, rfl, rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      all_goals norm_num 
    · -- Fourth solution (2, 2, 3, 3).
      simp [Prod.ext_iff] at h 
      rcases h with ⟨rfl, rfl, rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      all_goals norm_num