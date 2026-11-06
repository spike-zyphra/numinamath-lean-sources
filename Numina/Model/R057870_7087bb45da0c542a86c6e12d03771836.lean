import Mathlib

def isGood (a b c : ℕ) : Prop := a ≤ b ∧ b ≤ c ∧ a * b * c = 2 * (a + b + c)

theorem number_theory_302975 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ isGood a b c}.ncard = 3 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ isGood a b c} = {(1, 3, 8), (1, 4, 5), (2, 2, 4)} := by
    ext ⟨a, b, c⟩
    simp [isGood]
    constructor
    · -- Assume (a, b, c) satisfies the conditions, prove (a, b, c) ∈ {(1, 3, 8), (1, 4, 5), (2, 2, 4)}
      rintro ⟨ha, hb, hc, ⟨h₃, h₄, heq⟩⟩
      have h2 : a ≤ b := h₃
      have h3 : b ≤ c := h₄
      have h4 : a ≤ 2 := by
        nlinarith [mul_nonneg (show (b : ℕ) - a ≥ 0 by omega) (show (c : ℕ) - b ≥ 0 by omega), 
          heq, 
          mul_pos ha hb, 
          mul_pos hb hc, 
          mul_pos ha hc
        ]
      have h5 : a = 1 ∨ a = 2 := by
        omega
      rcases h5 with (rfl | rfl)
      · -- Case a = 1
        have h6 : b ≤ 8 := by
          nlinarith [heq, sq_nonneg (b : ℕ), sq_nonneg (c : ℕ), sq_nonneg (b - 1 : ℕ), sq_nonneg (c - 1 : ℕ), sq_nonneg (b - c : ℕ)]
        interval_cases b <;> omega
      · -- Case a = 2
        have h8 : b ≤ 4 := by
          nlinarith [heq, sq_nonneg (b : ℕ), sq_nonneg (c : ℕ), sq_nonneg (b - 1 : ℕ), sq_nonneg (c - 1 : ℕ), sq_nonneg (b - c : ℕ)]
        interval_cases b <;> omega
    · -- Assume (a, b, c) ∈ {(1, 3, 8), (1, 4, 5), (2, 2, 4)}, prove (a, b, c) satisfies the conditions
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
  <;> rfl