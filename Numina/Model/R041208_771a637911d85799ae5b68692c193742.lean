import Mathlib

theorem number_theory_22704 :
    IsGreatest {x | ∃ a b : ℕ, 0 < a ∧ a < 100 ∧ 0 < b ∧ b < 100 ∧ x = a + b ∧ Nat.gcd a b = 3 ∧ Nat.lcm a b = 12 * a} 129 := by
  constructor
  · -- Show that 129 is in the set.
    use 93, 36
    all_goals norm_num [Nat.lcm, Nat.gcd]
  · -- Show that 129 is greatest.
    intro x h
    rcases h with ⟨a, b, ha_pos, ha_lt, hb_pos, hb_lt, hx_eq, h_gcd, h_lcm⟩
    have h1 : a.gcd b * (a.lcm b) = a * b := by
      rw [Nat.gcd_mul_lcm]
    rw [h_gcd] at h1
    rw [h_lcm] at h1
    have h2 : b = 36 := by
      have h3 : 3 * (12 * a) = a * b := by
        linarith
      have h4 : a > 0 := by linarith
      have h5 : a < 100 := by linarith
      nlinarith [show a > 0 by linarith, show a < 100 by linarith]
    have h4 : a ≤ 99 := by
      linarith
    rw [h2] at h_gcd
    rw [h2] at h_lcm
    interval_cases a <;> norm_num [Nat.gcd, Nat.lcm] at h_gcd h_lcm hx_eq
    <;> omega