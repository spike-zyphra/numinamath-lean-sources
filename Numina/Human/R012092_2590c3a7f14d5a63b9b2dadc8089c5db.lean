import Mathlib

/- Determine all pairs (a;b) of natural numbers with
  a < b that have the following properties:
  The sum of the numbers
  a and b is 192.
  The greatest common divisor of the numbers a and b is 24. -/

theorem number_theory_174142: {(a, b): ℕ × ℕ | a < b ∧ a + b = 192 ∧
  a.gcd b = 24} = {(24, 168), (72, 120)} := by

    ext ⟨a, b⟩
    constructor

    -- the forward direction: show that the set is a subset of the right-hand side
    .
      intro h
      simp at h
      simp
      rcases h with ⟨l, h1, h2⟩
      replace h1: b = 192 - a := by omega
      rw [h1] at h2
      have o: a.gcd (192 - a) = a.gcd 192 := by
        nth_rewrite 2 [show 192 = 192 - a + a by omega]
        rw [Nat.gcd_add_self_right]
      rw [o] at h2
      clear o
      have d: 24 ∣ a := by
        rw [← h2]
        apply Nat.gcd_dvd_left
      apply exists_eq_mul_right_of_dvd at d
      obtain ⟨k, d⟩ := d
      have lk: k ≤ 8 := by omega
      interval_cases k
      all_goals simp [d] at h2
      all_goals simp [d, h1]
      .
        simp [h1, d] at l
      .
        simp [h1, d] at l

    -- the backward direction: verify that the right-hand side are true
    .
      intro h
      simp at h
      rcases h with h | h
      all_goals simp [h]
