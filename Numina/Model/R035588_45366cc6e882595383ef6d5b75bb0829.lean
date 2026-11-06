import Mathlib

theorem algebra_16391 (l : List ℕ) (hl : l = [1, 1, 5, 5, 10, 10, 25]) :
    Set.ncard {n : ℕ | ∃ i j : ℕ, i ≠ j ∧ i < l.length ∧ j < l.length ∧ n = l[i]! + l[j]!} = 9 := by
  rw [hl]
  have : {n : ℕ | ∃ i j : ℕ, i ≠ j ∧ i < ([1, 1, 5, 5, 10, 10, 25] : List ℕ).length ∧ j < ([1, 1, 5, 5, 10, 10, 25] : List ℕ).length ∧ n = ([1, 1, 5, 5, 10, 10, 25] : List ℕ)[i]! + ([1, 1, 5, 5, 10, 10, 25] : List ℕ)[j]!} = {2, 6, 10, 11, 15, 20, 26, 30, 35} := by
    ext n
    simp
    constructor
    · -- Assume that n is in the left side
      rintro ⟨i, j, hneq, hi, hj, hn⟩
      have h1 : i < 7 := by
        norm_num at hi ⊢
        omega
      have h2 : j < 7 := by
        norm_num at hj ⊢
        omega
      interval_cases i <;> interval_cases j
      <;> norm_num at hn hneq ⊢
      <;> omega
    · -- Assume that n is in the right side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 2
        use 0, 1
        all_goals norm_num
      · -- n = 6
        use 0, 2
        all_goals norm_num
      · -- n = 10
        use 2, 3
        all_goals norm_num
      · -- n = 11
        use 0, 4
        all_goals norm_num
      · -- n = 15
        use 2, 4
        all_goals norm_num
      · -- n = 20
        use 4, 5
        all_goals norm_num
      · -- n = 26
        use 0, 6
        all_goals norm_num
      · -- n = 30
        use 2, 6
        all_goals norm_num
      · -- n = 35
        use 4, 6
        all_goals norm_num
  rw [this]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }