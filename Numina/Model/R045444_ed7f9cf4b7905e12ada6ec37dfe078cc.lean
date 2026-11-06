import Mathlib

theorem number_theory_3365 :
    IsLeast {m : ℕ | ∃ a b, a > 0 ∧ b > 0 ∧ a + b = 2019 ∧ m = Nat.lcm a b} 1346 := by
  constructor
  · -- Show 1346 is in the set: use a = 673 and b = 1346
    use 673, 1346
    all_goals norm_num
  · -- Prove that 1346 is minimal.
    intro m hm
    rcases hm with ⟨a, b, ha, hb, hab1, hm⟩
    by_contra h
    push_neg at h
    have h1 : a ≤ 2019 := by
      linarith
    have h2 : b = 2019 - a := by
      omega
    rw [h2] at hm
    interval_cases a <;> norm_num [Nat.lcm] at hm h ⊢
    all_goals omega