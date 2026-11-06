import Mathlib

theorem inequalities_68070 :
    IsLeast {B : ℕ | {x : ℕ | x > Real.sqrt 15 ∧ x < (B : ℝ) ^ ((1 : ℝ) / 3)}.ncard = 13} 4097 := by
  constructor
  · simp
    have : {x : ℕ | √15 < ↑x ∧ ↑x < (4097 : ℝ) ^ ((1 : ℝ) / 3)} = {x : ℕ | 4 ≤ x ∧ x ≤ 16} := by
      ext x; simp
      constructor
      · intro ⟨h₁, h₂⟩
        have h₃ : 4 ≤ x := by
          have h₁ : 15 < x^2 := by
            rw [Real.sqrt_lt] at h₁
            norm_cast at h₁
            positivity
            simp
          by_contra!
          have h₂ := Nat.pow_lt_pow_left this (show 2 ≠ 0 by simp)
          linarith
        use h₃
        have h₄ : x^3 < 4097 := by
          rw [Real.lt_rpow_iff_log_lt] at h₂
          field_simp at h₂
          suffices (x : ℝ) ^ 3 < 4097 by norm_cast at this
          rw [Real.pow_lt_iff_lt_log]
          field_simp
          linarith
          repeat positivity
        by_contra!
        have h₂ := Nat.pow_lt_pow_left this (show 3 ≠ 0 by simp)
        linarith
      · intro ⟨h₁, h₂⟩
        split_ands
        · rw [Real.sqrt_lt]
          norm_cast
          have h₃ := Nat.pow_le_pow_left h₁ 2
          repeat linarith
        · have h₃ := Nat.pow_le_pow_left h₂ 3
          rw [Real.lt_rpow_inv_iff_of_pos]
          norm_cast
          repeat linarith
    simp at this
    rw [this, show {x : ℕ | 4 ≤ x ∧ x ≤ 16} = Finset.Icc 4 16 by ext x; simp]
    apply Set.ncard_coe_Finset
  · intro B hB
    simp at hB
    have : {x : ℕ | √15 < x ∧ x < (B : ℝ) ^ (3 : ℝ)⁻¹} = {x : ℕ | 4 ≤ x ∧ x < (B : ℝ) ^ (3 : ℝ)⁻¹} := by
      ext x; simp
      intro _
      constructor
      · intro h₁
        have h₁ : 15 < x^2 := by
          rw [Real.sqrt_lt] at h₁
          norm_cast at h₁
          positivity
          simp
        by_contra!
        have h₂ := Nat.pow_lt_pow_left this (show 2 ≠ 0 by simp)
        linarith
      · intro h₁
        rw [Real.sqrt_lt]
        norm_cast
        have h₃ := Nat.pow_le_pow_left h₁ 2
        repeat linarith
    obtain ⟨r, hr⟩ := show ∃r, {x : ℕ | 4 ≤ x ∧ x < (B : ℝ) ^ (3 : ℝ)⁻¹} = Finset.Icc 4 r by
      have h₄ : ⌊(B : ℝ) ^ (3 : ℝ)⁻¹⌋ = ⌊(B : ℝ) ^ (3 : ℝ)⁻¹⌋.natAbs := by
        apply Int.eq_natAbs_of_zero_le
        rw [Int.floor_nonneg]
        apply Real.rpow_nonneg
        positivity
      by_cases h₁: ∃ r : ℕ, r = (B : ℝ) ^ (3 : ℝ)⁻¹
      · rcases h₁ with ⟨r', hr'⟩
        use (r' - 1)
        ext x; simp
        intro h₂
        constructor
        · intro h₃
          rw [hr'.symm] at h₃
          norm_cast at h₃
          omega
        · intro h₃
          rw [hr'.symm]
          norm_cast
          omega
      use ⌊(B : ℝ) ^ (3 : ℝ)⁻¹⌋.natAbs
      ext x; simp
      intro h₂
      constructor
      · intro h₃
        suffices x ≤ ⌊(B : ℝ) ^ (3 : ℝ)⁻¹⌋ by
          rw [h₄] at this
          norm_cast at this
        rw [Int.le_floor]
        norm_cast
        linarith
      · intro h₃
        have : x ≤ ⌊(B : ℝ) ^ (3 : ℝ)⁻¹⌋ := by
          rw [h₄]
          norm_cast
        rw [Int.le_floor] at this
        norm_cast at this
        apply lt_of_le_of_ne this
        intro h₄
        rw [h₄.symm] at h₁
        simp at h₁
    rw [this, hr, Set.ncard_coe_Finset] at hB
    simp at hB
    rw [Nat.sub_eq_iff_eq_add] at hB
    rw [hB, Set.ext_iff] at hr
    simp at hr
    specialize hr 16 (by linarith)
    simp at hr
    rw [Real.lt_rpow_inv_iff_of_pos] at hr
    norm_cast at hr
    repeat linarith
    omega
