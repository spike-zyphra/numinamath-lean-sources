import Mathlib

open Real
open scoped BigOperators

theorem inequalities_189502 :
  Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 < 16 ∧ p.1^2 + p.2^2 < 8 * p.1 ∧ p.1^2 + p.2^2 < 8 * p.2} = 6 := by

  have h1 : {p : ℤ × ℤ | p.1^2 + p.2^2 < 16 ∧ p.1^2 + p.2^2 < 8 * p.1 ∧ p.1^2 + p.2^2 < 8 * p.2} = {(1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · rintro ⟨h1, h2, h3⟩

      -- Show that a and b must be positive
      have h4 : a > 0 := by nlinarith [sq_nonneg (a), sq_nonneg (b)]
      have h5 : b > 0 := by nlinarith [sq_nonneg (a), sq_nonneg (b)]

      -- Show upper bounds
      have h6 : a ≤ 4 := by nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 2)]
      have h7 : b ≤ 4 := by nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 3)]

      interval_cases a <;> interval_cases b 
      <;> norm_num at h1 h2 h3 
      <;> omega

    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        constructor
        · norm_num
        all_goals
          constructor
          · norm_num
          · norm_num

  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }