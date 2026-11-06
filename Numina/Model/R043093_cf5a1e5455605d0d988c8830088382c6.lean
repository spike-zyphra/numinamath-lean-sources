import Mathlib
import Aesop

theorem algebra_14646 : ∃(S: Set (ℕ × ℕ)), S = { (a, b) | 0 < a ∧ 0 < b ∧ a ≤ b ∧ a * b = 2 * (2 * a + 2 * b) } ∧ ∃(r : Finset (ℕ × ℕ)), r = S ∧ ∑ p ∈ r, p.1 * p.2 = 236 := by
  use { (5, 20), (6, 12), (8, 8) }
  constructor
  · -- Show the equality of sets.
    ext ⟨a, b⟩ 
    simp 
    constructor 
    · -- Show that if (a, b) ∈ {(5, 20), (6, 12), (8, 8)}, then it's in S.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (5, 20)
        constructor
        · norm_num
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num
      · -- (6, 12)
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num
      · -- (8, 8)
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
    · -- Show the reverse direction.
      rintro ⟨ha, hb, hab, heq⟩
      have h1 : a * b = 4 * (a + b) := by 
        nlinarith
      have h2 : a ≤ 20 := by
        by_contra h 
        push_neg at h
        have h3 : b ≤ 4 := by 
          nlinarith [h1, h]
        interval_cases b <;> omega
      have h3 : b ≤ 20 := by
        by_contra h 
        push_neg at h
        have h4 : a ≤ 4 := by 
          nlinarith [h1, h]
        interval_cases a <;> omega 
      interval_cases a <;> omega 
  · -- Show the existence of the finite set r
    use {(5, 20), (6, 12), (8, 8)}
    constructor
    · -- Show r = S
      ext ⟨a, b⟩ 
      simp 
    · -- Show the summation
      native_decide