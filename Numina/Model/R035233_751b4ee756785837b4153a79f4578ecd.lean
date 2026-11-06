import Mathlib

theorem number_theory_15944 :
  {(a, b) : ℕ × ℕ | a * b = 1995 ∧ a ∈ Finset.Icc 10 99 ∧ b ∈ Finset.Icc 10 99 ∧ a ≤ b}.ncard = 2 := by
  have h1 : {(a, b) : ℕ × ℕ | a * b = 1995 ∧ a ∈ Finset.Icc 10 99 ∧ b ∈ Finset.Icc 10 99 ∧ a ≤ b} = {(21, 95), (35, 57)} := by
    ext ⟨a, b⟩
    simp [Finset.mem_Icc]
    constructor
    · -- Assume (a, b) in the set
      rintro ⟨h_eq, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hle⟩
      interval_cases a <;> omega
    · -- Show that (21, 95) and (35, 57) are in the set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (21, 95)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (35, 57)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]
  all_goals norm_num