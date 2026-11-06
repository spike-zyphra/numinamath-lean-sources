import Mathlib

theorem number_theory_13514 : IsLeast {x : ℕ | 0 < x ∧ 3 * x ≡ 4 [MOD 7] ∧ 7 * x ≡ 9 [MOD 11]} 6 := by
  constructor
  · -- Show that 6 is in the set
    constructor
    · -- Show that 6 > 0
      norm_num
    constructor
    · -- Show that 3 * 6 ≡ 4 [MOD 7]
      simp [Nat.ModEq]
      all_goals norm_num
    · -- Show that 7 * 6 ≡ 9 [MOD 11]
      simp [Nat.ModEq]
      all_goals norm_num
  · -- Show that any x in the set is ≥ 6
    intro y hy
    rcases hy with ⟨hy_pos, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : y < 6 := by linarith
    interval_cases y <;> simp [Nat.ModEq] at h1 h2 <;> all_goals omega