import Mathlib

theorem number_theory_174142: {(a, b): ℕ × ℕ | a < b ∧ a + b = 192 ∧
  a.gcd b = 24} = {(24, 168), (72, 120)} := by
  ext ⟨a, b⟩
  constructor
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
    obtain ⟨k, h3⟩ := d
    have h4: k ≤ 8 := by
      omega
    interval_cases k
    all_goals simp [h3] at h4
    all_goals simp [h3, h1] at h2
    all_goals simp [h3, h1, h2, h4] at l ⊢
  .
    intro h
    simp at h
    rcases h with h | h
    all_goals simp [h]