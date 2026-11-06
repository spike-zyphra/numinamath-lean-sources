import Mathlib

theorem number_theory_34457:
    IsLeast {k : ℤ | 100 < k ∧ ∃ m n, 221*m+247*n+323*k=2001} 111 := by
  constructor
  · -- Show k=111 satisfies the conditions
    constructor
    · -- Show k=111 > 100
      norm_num
    · -- Show there exist integers m, n with the equation
      use -23436, 20832
      all_goals norm_num
  · -- Show k=111 is the least such k > 100
    intro k hk
    rcases hk with ⟨hk1, ⟨m, n, h⟩⟩
    by_contra h'
    push_neg at h'
    have h1 : k < 111 := by omega
    have h2 : k > 100 := by omega
    have h4 : (221 * m + 247 * n : ℤ) % 13 = 0 := by
      omega
    omega