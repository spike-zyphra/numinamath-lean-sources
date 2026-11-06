import Mathlib

theorem inequalities_6504 :
    Set.encard {x : ℤ | -6 < (6 - 3 * x) / (2 : ℚ) ∧ (6 - 3 * x) / (2 : ℚ) ≤ 8} = 9 := by
  have h1 : {x : ℤ | -6 < (6 - 3 * x) / (2 : ℚ) ∧ (6 - 3 * x) / (2 : ℚ) ≤ 8} = {-3, -2, -1, 0, 1, 2, 3, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x is in the set, we need to show it's in the finite set.
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : (6 - 3 * x : ℚ) / 2 > -6 := by linarith
      have h4 : (6 - 3 * x : ℚ) / 2 ≤ (8 : ℚ) := by linarith
      have h5 : (6 - 3 * x : ℚ) > -12 := by
        linarith
      have h6 : (6 - 3 * x : ℚ) ≤ 16 := by
        linarith
      have h7 : (6 - 3 * x : ℤ) > -12 := by
        exact_mod_cast h5
      have h8 : (6 - 3 * x : ℤ) ≤ 16 := by
        exact_mod_cast h6
      omega
    · -- Assume x is in the finite set, we need to show it's in the set.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = -3
        constructor
        · norm_num
        · norm_num
      · -- x = -2
        constructor
        · norm_num
        · norm_num
      · -- x = -1
        constructor
        · norm_num
        · norm_num
      · -- x = 0
        constructor
        · norm_num
        · norm_num
      · -- x = 1
        constructor
        · norm_num
        · norm_num
      · -- x = 2
        constructor
        · norm_num
        · norm_num
      · -- x = 3
        constructor
        · norm_num
        · norm_num
      · -- x = 4
        constructor
        · norm_num
        · norm_num
      · -- x = 5
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp
  <;> try { native_decide }