import Mathlib

theorem number_theory_610642 : IsGreatest
  {m | ∃ a b : ℕ, m = a + b ∧ 0 < a ∧ a ≤ 100 ∧
  0 < b ∧ b ≤ 100 ∧ a * b = (a.lcm b / a.gcd b) ^ 2} 78 := by

  constructor
  · -- Show that 78 belongs to the set.
    use 54, 24
    all_goals norm_num
  · -- Show that 78 is greatest in the set.
    intro m
    rintro ⟨a, b, rfl, ha_pos, ha_le, hb_pos, hb_le, h_eq⟩
    interval_cases a <;> interval_cases b <;> norm_num [Nat.lcm, Nat.gcd] at h_eq ⊢ <;> omega