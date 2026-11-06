import Mathlib

theorem number_theory_297134
    (a b c : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    10 ∣ a^3 * b - a * b^3 ∨ 10 ∣ b^3 * c - b * c^3 ∨ 10 ∣ c^3 * a - c * a^3 := by

  have h1 : (a ^ 3 * b - a * b ^ 3) % 2 = 0 := by
    have ha1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb1 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases ha1 with (ha1 | ha1)
    ·
      have h2 : (a ^ 3 * b - a * b ^ 3) % 2 = 0 := by
        simp [Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod, ha1, hb1]
      omega
    ·
      rcases hb1 with (hb1 | hb1)
      · 
        have h2 : (a ^ 3 * b - a * b ^ 3) % 2 = 0 := by
          simp [Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod, ha1, hb1]
        omega
      ·
        have h2 : (a ^ 3 * b - a * b ^ 3) % 2 = 0 := by
          simp [Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod, ha1, hb1]
        omega

  have h2 : (b ^ 3 * c - b * c ^ 3) % 2 = 0 := by
    have hb1 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    have hc1 : c % 2 = 0 ∨ c % 2 = 1 := by omega
    rcases hb1 with (hb1 | hb1)
    ·
      have h3 : (b ^ 3 * c - b * c ^ 3) % 2 = 0 := by
        simp [Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod, hb1, hc1]
      omega
    ·
      rcases hc1 with (hc1 | hc1)
      · 
        have h3 : (b ^ 3 * c - b * c ^ 3) % 2 = 0 := by
          simp [Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod, hb1, hc1]
        omega
      ·
        have h3 : (b ^ 3 * c - b * c ^ 3) % 2 = 0 := by
          simp [Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod, hb1, hc1]
        omega

  have h3 : (c ^ 3 * a - c * a ^ 3) % 2 = 0 := by
    have hc1 : c % 2 = 0 ∨ c % 2 = 1 := by omega
    have ha1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases hc1 with (hc1 | hc1)
    ·
      have h4 : (c ^ 3 * a - c * a ^ 3) % 2 = 0 := by
        simp [Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod, hc1, ha1]
      omega
    ·
      rcases ha1 with (ha1 | ha1)
      · 
        have h4 : (c ^ 3 * a - c * a ^ 3) % 2 = 0 := by
          simp [Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod, hc1, ha1]
        omega
      ·
        have h4 : (c ^ 3 * a - c * a ^ 3) % 2 = 0 := by
          simp [Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod, hc1, ha1]
        omega

  have h4 : (a ^ 3 * b - a * b ^ 3) % 5 = 0 ∨ (b ^ 3 * c - b * c ^ 3) % 5 = 0 ∨ (c ^ 3 * a - c * a ^ 3) % 5 = 0 := by

    by_cases h1 : a % 5 = 0
    · 
      have h10 : (a ^ 3 * b - a * b ^ 3) % 5 = 0 := by
        simp [Int.mul_emod, Int.sub_emod, pow_succ, h1, Int.mul_emod, Int.sub_emod]
      left
      tauto
    by_cases h2 : b % 5 = 0
    · 
      have h10 : (a ^ 3 * b - a * b ^ 3) % 5 = 0 := by
        simp [Int.mul_emod, Int.sub_emod, pow_succ, h2, Int.mul_emod, Int.sub_emod]
      left
      tauto
    by_cases h3 : c % 5 = 0
    · 
      have h10 : (b ^ 3 * c - b * c ^ 3) % 5 = 0 := by
        simp [Int.mul_emod, Int.sub_emod, pow_succ, h3, Int.mul_emod, Int.sub_emod]
      right
      left
      tauto
    · 
      have ha1 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
        omega
      have hb1 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by
        omega
      have hc1 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by
        omega
      have h4 : (a ^ 2 : ℤ) % 5 = 1 ∨ (a ^ 2 : ℤ) % 5 = 4 := by
        have h1 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := ha1
        rcases h1 with (h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      have h5 : (b ^ 2 : ℤ) % 5 = 1 ∨ (b ^ 2 : ℤ) % 5 = 4 := by
        have h1 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := hb1
        rcases h1 with (h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      have h6 : (c ^ 2 : ℤ) % 5 = 1 ∨ (c ^ 2 : ℤ) % 5 = 4 := by
        have h1 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := hc1
        rcases h1 with (h1 | h1 | h1 | h1) <;> 
          simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      have h7 : (a ^ 2 : ℤ) % 5 = (b ^ 2 : ℤ) % 5 ∨ (b ^ 2 : ℤ) % 5 = (c ^ 2 : ℤ) % 5 ∨ (a ^ 2 : ℤ) % 5 = (c ^ 2 : ℤ) % 5 := by
        omega
      rcases h7 with (h7 | h7 | h7)
      · 
        have h8 : (a ^ 3 * b - a * b ^ 3) % 5 = 0 := by
          have h15 : (a ^ 2 : ℤ) % 5 = (b ^ 2 : ℤ) % 5 := h7
          have h12 : (a ^ 3 * b - a * b ^ 3) % 5 = 0 := by
            have h10 : (a ^ 3 * b - a * b ^ 3) = a * b * (a ^ 2 - b ^ 2) := by 
              ring
            have h11 : (a * b * (a ^ 2 - b ^ 2)) % 5 = 0 := by
              have h13 : (a ^ 2 - b ^ 2) % 5 = 0 := by
                have h14 : (a ^ 2 : ℤ) % 5 = (b ^ 2 : ℤ) % 5 := h15
                omega
              have h14 : (a * b * (a ^ 2 - b ^ 2)) % 5 = 0 := by
                simp [Int.mul_emod, h13, Int.mul_emod, Int.sub_emod]
              omega
            rw [h10]
            all_goals omega
          omega
        left
        omega
      · 
        have h8 : (b ^ 3 * c - b * c ^ 3) % 5 = 0 := by
          have h15 : (b ^ 2 : ℤ) % 5 = (c ^ 2 : ℤ) % 5 := h7
          have h12 : (b ^ 3 * c - b * c ^ 3) % 5 = 0 := by
            have h10 : (b ^ 3 * c - b * c ^ 3) = b * c * (b ^ 2 - c ^ 2) := by 
              ring
            have h11 : (b * c * (b ^ 2 - c ^ 2)) % 5 = 0 := by
              have h13 : (b ^ 2 - c ^ 2) % 5 = 0 := by
                have h14 : (b ^ 2 : ℤ) % 5 = (c ^ 2 : ℤ) % 5 := h15
                omega
              have h14 : (b * c * (b ^ 2 - c ^ 2)) % 5 = 0 := by
                simp [Int.mul_emod, h13, Int.mul_emod, Int.sub_emod]
              omega
            rw [h10]
            all_goals omega
          omega
        right
        left
        omega
      · 
        have h8 : (c ^ 3 * a - c * a ^ 3) % 5 = 0 := by
          have h15 : (a ^ 2 : ℤ) % 5 = (c ^ 2 : ℤ) % 5 := h7
          have h12 : (c ^ 3 * a - c * a ^ 3) % 5 = 0 := by
            have h10 : (c ^ 3 * a - c * a ^ 3) = c * a * (c ^ 2 - a ^ 2) := by 
              ring
            have h11 : (c * a * (c ^ 2 - a ^ 2)) % 5 = 0 := by
              have h13 : (c ^ 2 - a ^ 2) % 5 = 0 := by
                have h14 : (a ^ 2 : ℤ) % 5 = (c ^ 2 : ℤ) % 5 := h15
                have h15 : (c ^ 2 : ℤ) % 5 = (a ^ 2 : ℤ) % 5 := by 
                  omega
                omega
              have h14 : (c * a * (c ^ 2 - a ^ 2)) % 5 = 0 := by
                simp [Int.mul_emod, h13, Int.mul_emod, Int.sub_emod]
              omega
            rw [h10]
            all_goals omega
          omega
        right
        right
        omega

  omega