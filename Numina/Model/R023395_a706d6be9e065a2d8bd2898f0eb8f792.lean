import Mathlib

theorem number_theory_181670 (a b : ℕ) :
    a^2 - b^2 = 2023 ↔ (a = 1012 ∧ b = 1011) ∨ (a = 148 ∧ b = 141) ∨ (a = 68 ∧ b = 51) := by
  constructor
  · -- Forward implication: if a^2 - b^2 = 2023 then the pair is one of these
    intro h
    have h1 : a^2 = b^2 + 2023 := by
      omega
    have h2 : a > b := by
      by_contra h'
      push_neg at h'
      have h3 : a ≤ b := by
        omega
      nlinarith [h1, sq_nonneg (a : ℕ), sq_nonneg (b : ℕ), sq_nonneg (a - b : ℤ)]
    have h3 : (a : ℤ) ^ 2 = (b : ℤ) ^ 2 + 2023 := by
      exact_mod_cast h1
    have h5 : ((a : ℤ) - (b : ℤ)) * ((a : ℤ) + (b : ℤ)) = 2023 := by
      nlinarith
    have h6 : (a - b : ℤ) * (a + b : ℤ) = 2023 := by
      exact_mod_cast h5

    have h11 : (a - b : ℤ) ∣ 2023 := by
      use (a + b : ℤ)
      linarith
    have h12 : (a - b : ℤ) ≥ 1 := by
      omega
    have h13 : (a - b : ℤ) ≤ 2023 := by
      have h55 : (a - b : ℤ) ∣ 2023 := h11
      exact Int.le_of_dvd (show 0 < 2023 by norm_num) h55
    have h14 : (a - b : ℤ) ≥ 1 := h12
    have h15 : (a - b : ℤ) ≤ 2023 := h13
    have h16 : (a - b : ℤ) = 1 ∨ (a - b : ℤ) = 7 ∨ (a - b : ℤ) = 17 ∨ (a - b : ℤ) = 119 ∨ (a - b : ℤ) = 289 ∨ (a - b : ℤ) = 2023 := by
      interval_cases k : (a - b : ℤ) <;> tauto
      <;> omega
      <;> try { 
          norm_num at h11 
          all_goals omega 
        }
    rcases h16 with (h21 | h22 | h23 | h24 | h25 | h26)
    · -- Case where a - b = 1
      have h71 : (a - b : ℤ) = 1 := h21
      have h72 : (a + b : ℤ) = 2023 := by
        nlinarith [h6, h71]
      have h73 : (a : ℤ) = 1012 := by
        omega
      have h74 : (b : ℤ) = 1011 := by
        omega
      norm_cast at h73 h74
      left
      exact ⟨h73, h74⟩
    · -- Case where a - b = 7
      have h71 : (a - b : ℤ) = 7 := h22
      have h72 : (a + b : ℤ) = 289 := by
        nlinarith [h6, h71]
      have h73 : (a : ℤ) = 148 := by
        omega
      have h74 : (b : ℤ) = 141 := by
        omega
      norm_cast at h73 h74
      right
      left
      exact ⟨h73, h74⟩
    · -- Case where a - b = 17
      have h71 : (a - b : ℤ) = 17 := h23
      have h72 : (a + b : ℤ) = 119 := by
        nlinarith [h6, h71]
      have h73 : (a : ℤ) = 68 := by
        omega
      have h74 : (b : ℤ) = 51 := by
        omega
      norm_cast at h73 h74
      right
      right
      exact ⟨h73, h74⟩
    · -- Case where a - b = 119
      have h71 : (a - b : ℤ) = 119 := h24
      have h72 : (a + b : ℤ) = 17 := by
        nlinarith [h6, h71]
      have h73 : (a : ℤ) ≤ (b : ℤ) := by
        omega
      exfalso
      omega
    · -- Case where a - b = 289
      have h71 : (a - b : ℤ) = 289 := h25
      have h72 : (a + b : ℤ) = 7 := by
        nlinarith [h6, h71]
      have h73 : (a : ℤ) ≤ (b : ℤ) := by
        omega
      exfalso
      omega
    · -- Case where a - b = 2023
      have h71 : (a - b : ℤ) = 2023 := h26
      have h72 : (a + b : ℤ) = 1 := by
        nlinarith [h6, h71]
      have h73 : (a : ℤ) ≤ (b : ℤ) := by
        omega
      exfalso
      omega
  · -- Backward implication: the given pairs satisfy a^2 - b^2 = 2023
    rintro (h | h | h)
    · -- Check first pair
      rcases h with ⟨rfl, rfl⟩
      all_goals
      norm_num
    · -- Check second pair
      rcases h with ⟨rfl, rfl⟩
      all_goals
      norm_num
    · -- Check third pair
      rcases h with ⟨rfl, rfl⟩
      all_goals
      norm_num