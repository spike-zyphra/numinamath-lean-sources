import Mathlib

theorem inequalities_189162 :
    Set.ncard {(a, b) : ℤ × ℤ | a^2 + b^2 < 16 ∧ a^2 + b^2 < 8 * a ∧ a^2 + b^2 < 8 * b} = 6 := by
  have h1 : {(a, b) : ℤ × ℤ | a^2 + b^2 < 16 ∧ a^2 + b^2 < 8 * a ∧ a^2 + b^2 < 8 * b} = { (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2) } := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Forward direction: if (a, b) is in the set, it's one of the six pairs.
      rintro ⟨h1, h2, h3⟩
      have h4 : a > 0 := by
        nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 4), sq_nonneg (a), sq_nonneg (b)]
      have h5 : b > 0 := by
        nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 4), sq_nonneg (a), sq_nonneg (b)]
      have h4' : a ≤ 3 := by
        nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 3), sq_nonneg (a), sq_nonneg (b)]
      have h5' : b ≤ 3 := by
        nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 3), sq_nonneg (a), sq_nonneg (b)]
      interval_cases a <;> interval_cases b
      <;> omega
    · -- Backward direction: each pair in the finite set is in the actual set.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (1, 1)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (1, 2)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (2, 1)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (2, 2)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (2, 3)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (3, 2)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
  <;> try { native_decide }