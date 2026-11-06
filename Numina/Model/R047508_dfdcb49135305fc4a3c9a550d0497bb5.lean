import Mathlib

theorem algebra_134088 (z : ℤ) (hz : z ≠ 1) :
    ∃ k : ℤ, (5 * z ^ 2 + 3) / (z - 1) = k ↔
    z = -7 ∨ z = -3 ∨ z = -1 ∨ z = 0 ∨ z = 2 ∨ z = 3 ∨ z = 5 ∨ z = 9 := by 
  by_cases h : z = -7 ∨ z = -3 ∨ z = -1 ∨ z = 0 ∨ z = 2 ∨ z = 3 ∨ z = 5 ∨ z = 9
  · -- Assume z is in the solution set
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- Case z = -7
      use -31
      all_goals norm_num
    · -- Case z = -3
      use -12
      all_goals norm_num
    · -- Case z = -1
      use -4
      all_goals norm_num
    · -- Case z = 0
      use -3
      all_goals norm_num
    · -- Case z = 2
      use 23
      all_goals norm_num
    · -- Case z = 3
      use 24
      all_goals norm_num
    · -- Case z = 5
      use 32
      all_goals norm_num
    · -- Case z = 9
      use 51
      all_goals norm_num
  · -- Assume z is not in the solution set
    have h2 : z ≠ -7 := by
      intro h'
      apply h
      tauto
    have h3 : z ≠ -3 := by
      intro h'
      apply h
      tauto
    have h4 : z ≠ -1 := by
      intro h'
      apply h
      tauto
    have h5 : z ≠ 0 := by
      intro h'
      apply h
      tauto
    have h6 : z ≠ 2 := by
      intro h'
      apply h
      tauto
    have h7 : z ≠ 3 := by
      intro h'
      apply h
      tauto
    have h8 : z ≠ 5 := by
      intro h'
      apply h
      tauto
    have h9 : z ≠ 9 := by
      intro h'
      apply h
      tauto
    use (5 * z ^ 2 + 3) / (z - 1) + 1
    have h10 : (5 * z ^ 2 + 3) / (z - 1) ≠ (5 * z ^ 2 + 3) / (z - 1) + 1 := by 
      omega
    simp_all [h10]
    all_goals try { omega }