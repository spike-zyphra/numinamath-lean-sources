import Mathlib

theorem number_theory_2655 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x^2 * y = 180}.encard = 4 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x^2 * y = 180} = {(1, 180), (2, 45), (3, 20), (6, 5)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · rintro ⟨hx, hy, h⟩
      have h2 : x ≤ 13 := by
        by_contra h2
        push_neg at h2
        have h3 : x ^ 2 * y = 180 := h
        have h4 : x ^ 2 ≥ 14 ^ 2 := by
          have h5 : x ≥ 14 := by linarith
          have h6 : x ^ 2 ≥ 14 ^ 2 := by
            apply Nat.pow_le_pow_of_le_left h5 2
          linarith
        have h5 : y ≥ 1 := by nlinarith
        have h6 : x ^ 2 * y ≥ 14 ^ 2 * 1 := by
          nlinarith [h4, h5]
        have h7 : x ^ 2 * y > 180 := by
          norm_num at h6 ⊢
          linarith
        linarith [h3, h7]
      interval_cases x <;> omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { rfl }
  <;> try { aesop }