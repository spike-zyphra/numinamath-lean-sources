import Mathlib

theorem number_theory_202373 :
    (16 < 33 ∧ 33 < 34 ∧ 34 < 43 ∧ 43 < 61) ∧ ({n : ℕ | n ∈ Finset.Ioo 76 84 ∧ Odd n} = {77, 79, 81, 83}) := by
  constructor
  · -- Show that 16 < 33 ∧ 33 < 34 ∧ 34 < 43 ∧ 43 < 61
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that {n : ℕ | n ∈ Finset.Ioo 76 84 ∧ Odd n} = {77, 79, 81, 83}
    ext n
    simp [Finset.mem_Ioo, Nat.odd_iff]
    constructor
    · -- Forward direction: if n is in the set, then n ∈ {77, 79, 81, 83}
      rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : n ≥ 77 := by omega
      have h5 : n ≤ 83 := by omega
      interval_cases n <;> tauto
    · -- Backward direction: if n ∈ {77, 79, 81, 83}, then n is in the set.
      rintro (rfl | rfl | rfl | rfl)
      · -- Show that 77 is in the set.
        constructor
        · -- Show that 77 ∈ Finset.Ioo 76 84
          norm_num [Finset.mem_Ioo]
        · -- Show that 77 is odd.
          decide
      · -- Show that 79 is in the set.
        constructor
        · -- Show that 79 ∈ Finset.Ioo 76 84
          norm_num [Finset.mem_Ioo]
        · -- Show that 79 is odd.
          decide
      · -- Show that 81 is in the set.
        constructor
        · -- Show that 81 ∈ Finset.Ioo 76 84
          norm_num [Finset.mem_Ioo]
        · -- Show that 81 is odd.
          decide
      · -- Show that 83 is in the set.
        constructor
        · -- Show that 83 ∈ Finset.Ioo 76 84
          norm_num [Finset.mem_Ioo]
        · -- Show that 83 is odd.
          decide