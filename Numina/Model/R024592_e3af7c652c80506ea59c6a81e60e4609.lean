import Mathlib

theorem algebra_224710 :
    Set.ncard {p : (ℕ × ℕ) | p.1 > 0 ∧ p.2 > 0 ∧ p.1 * p.2 + p.1 = p.2 + 92} = 3 := by
  have h1 : {p : (ℕ × ℕ) | p.1 > 0 ∧ p.2 > 0 ∧ p.1 * p.2 + p.1 = p.2 + 92} = {(2, 90), (8, 12), (14, 6)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume ⟨x, y⟩ is in the set.
      rintro ⟨hx, hy, h_eq⟩
      have h2 : x ≤ 91 := by
        by_contra h
        push_neg at h
        have h3 : x * y + x > y + 92 := by
          have h4 : x ≥ 92 := by linarith
          have h5 : y ≥ 1 := by linarith
          nlinarith
        linarith
      interval_cases x <;> omega
    · -- Show that these three pairs are in the set.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (2, 90)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (8, 12)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (14, 6)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }