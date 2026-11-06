import Mathlib

theorem algebra_295213 (a : ℝ) (ha : a ≠ 0) :
    ∃ m n : ℤ, a + 2 / 3 = m ∧ 1 / a - 3 / 4 = n ↔ a = 4 / 3 := by
  use 2, 0
  constructor
  · -- Forward direction: If a + 2/3 = 2 and 1/a - 3/4 = 0 then a = 4/3
    intro h
    rcases h with ⟨h1, h2⟩
    norm_num at h1 h2
    have ha_eq : a = 4 / 3 := by
      field_simp [ha] at h2
      linarith
    linarith
  · -- Backward direction: If a = 4/3 then a + 2/3 = 2 and 1/a - 3/4 = 0
    intro h
    rw [h]
    constructor <;> norm_num