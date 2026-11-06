import Mathlib

theorem number_theory_190556: {(x, y): ℤ × ℤ | x * y = 1987}.encard = 4 := by
  have h1 : {(x, y) : ℤ × ℤ | x * y = 1987} = {(-1987, -1), (-1, -1987), (1, 1987), (1987, 1)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Forward implication: If (x, y) is in the left side, it's in the right side.
      rintro H
      have h2 : x ∣ 1987 := by
        use y
        linarith
      have h3 : x = 1 ∨ x = -1 ∨ x = 1987 ∨ x = -1987 := by
        have h4 : x ∣ 1987 := h2
        have h5 : x ≤ 1987 := by
          apply Int.le_of_dvd (by norm_num) h4
        have h6 : x ≥ -1987 := by
          have h7 : (-x) ∣ 1987 := by
            exact Int.neg_dvd.2 h4
          have h8 : -x ≤ 1987 := by
            apply Int.le_of_dvd (by norm_num) h7
          linarith
        interval_cases x <;> tauto
      rcases h3 with (r | r | r | r)
      · -- x = 1
        rw [r] at H
        have hy1 : y = 1987 := by
          linarith
        simp [hy1, r]
      · -- x = -1
        rw [r] at H
        have hy1 : y = -1987 := by
          linarith
        simp [hy1, r]
      · -- x = 1987
        rw [r] at H
        have hy1 : y = 1 := by
          linarith
        simp [hy1, r]
      · -- x = -1987
        rw [r] at H
        have hy1 : y = -1 := by
          linarith
        simp [hy1, r]
    · -- Backward implication
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (-1987, -1)
        norm_num
      · -- (-1, -1987)
        norm_num
      · -- (1, 1987)
        norm_num
      · -- (1987, 1)
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }