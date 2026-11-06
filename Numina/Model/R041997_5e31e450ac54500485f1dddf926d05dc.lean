import Mathlib

theorem algebra_155143 :
    {(a, b, c) : ℝ × ℝ × ℝ | a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a = b * c ∧ b = a * c ∧ c = a * b}.ncard = 4 := by

  have h1 : {(a, b, c) : ℝ × ℝ × ℝ | a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a = b * c ∧ b = a * c ∧ c = a * b} = {(-1, 1, -1), (-1, -1, 1), (1, -1, -1), (1, 1, 1)} := by
    ext ⟨a, b, c⟩
    simp
    constructor
    · -- Assume (a, b, c) satisfies all the conditions
      rintro ⟨ha, hb, hc, h1, h2, h3⟩

      have h4 : b ^ 2 = 1 := by
        have h5 : c = a * b := by linarith
        rw [h5] at h1
        have h6 : a = b * (a * b) := by linarith
        have h7 : a = a * (b ^ 2) := by
          ring_nf at h6 ⊢
          nlinarith
        have h8 : a * (1 - b ^ 2) = 0 := by
          linarith
        cases (mul_eq_zero.mp h8) with
        | inl h9 => 
          exfalso
          apply ha
          linarith 
        | inr h10 => 
          nlinarith

      have h6 : b = 1 ∨ b = -1 := by 
        have h7 : b ^ 2 = 1 := h4
        have : b = 1 ∨ b = -1 := by 
          rw [sq_eq_one_iff] at h7 
          tauto 
        assumption

      rcases h6 with (h7 | h7)
      · -- Case b = 1
        have h8 : a = c := by 
          rw [h7] at h1
          nlinarith 
        have h9 : 1 = a * c := by 
          rw [h7] at h2 
          linarith 
        have h10 : a ^ 2 = 1 := by 
          rw [show c = a by linarith [h8]] at h9 
          nlinarith 
        have h11 : a = 1 ∨ a = -1 := by
          have h13 : a ^ 2 = 1 := h10
          have : a = 1 ∨ a = -1 := by 
            rw [sq_eq_one_iff] at h13 
            tauto 
          assumption 
        rcases h11 with (h12 | h12)
        · -- Case a = 1
          have h13 : c = 1 := by 
            nlinarith [h8, h12] 
          simp [h12, h7, h13]
        · -- Case a = -1
          have h14 : c = -1 := by 
            nlinarith [h8, h12] 
          simp [h12, h7, h14]
      · -- Case b = -1
        have h8 : a = -c := by 
          rw [h7] at h1 
          linarith 
        have h10 : -1 = a * c := by 
          rw [h7] at h2 
          linarith 
        have h9 : c ^ 2 = 1 := by 
          rw [show a = -c by linarith [h8]] at h10 
          nlinarith 
        have h11 : c = 1 ∨ c = -1 := by
          have h13 : c ^ 2 = 1 := h9
          have : c = 1 ∨ c = -1 := by 
            rw [sq_eq_one_iff] at h13 
            tauto 
          assumption 
        rcases h11 with (h12 | h12)
        · -- Case c = 1
          have h13 : a = -1 := by 
            nlinarith [h8, h12] 
          simp [h13, h7, h12]
        · -- Case c = -1
          have h14 : a = 1 := by 
            nlinarith [h8, h12] 
          simp [h14, h7, h12]
    · -- Show the reverse direction
      rintro (h | h | h | h)
      · -- First quadruple
        rcases h with ⟨rfl, rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Second quadruple
        rcases h with ⟨rfl, rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Third quadruple
        rcases h with ⟨rfl, rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Fourth quadruple
        rcases h with ⟨rfl, rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num

  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> norm_num