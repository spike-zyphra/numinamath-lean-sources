import Mathlib

theorem number_theory_93319 (n : ℕ) (h : IsGreatest {n | ∃ (a b c d : ℕ), 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ 7 ∣ 1000 + 100 * b + 10 * c + d ∧ 7 ∣ 1000 * a + 100 + 10 * c + d ∧ 7 ∣ 1000 * a + 100 * b + 10 + d ∧ 7 ∣ 1000 * a + 100 * b + 10 * c + 1} n) : n / 1000 + n % 1000 = 699 := by

  have ta : IsGreatest {n | ∃ (a b c d : ℕ), 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ 7 ∣ 1000 + 100 * b + 10 * c + d ∧ 7 ∣ 1000 * a + 100 + 10 * c + d ∧ 7 ∣ 1000 * a + 100 * b + 10 + d ∧ 7 ∣ 1000 * a + 100 * b + 10 * c + 1} 5694 := by
    clear n h
    constructor
    · -- Show 5694 is in the set.
      exists 5, 6, 9, 4
      all_goals norm_num
    · -- Show 5694 is greatest in the set
      intros n hn
      obtain ⟨a, b, c, d, hn, hh, ha, hb, hc, hd, s1, s2, s3, s4⟩ := hn
      by_cases u : n ≤ 5694
      · exact u
      have v : 5695 ≤ n := by linarith
      clear u

      have q1 : 7 ∣ 1000 + 100 * b + 10 * c + d := by clear * - s1; omega
      have q2 : 7 ∣ 1000 * a + 100 + 10 * c + d := by clear * - s2; omega
      have q3 : 7 ∣ 1000 * a + 100 * b + 10 + d := by clear * - s3; omega
      have q4 : 7 ∣ 1000 * a + 100 * b + 10 * c + 1 := by clear * - s4; omega

      zify at q1 q2 q3 q4

      have d1 := Int.dvd_sub q2 q1
      have d2 := Int.dvd_sub q3 q2
      have d3 := Int.dvd_sub q4 q3
      have d4 := Int.dvd_sub q4 q1
      ring_nf at d1 d2 d3 d4

      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 5 := by clear * - hn hh; omega

      all_goals try (clear * - hd v hh ha hb hc; omega)
      all_goals (ring_nf at *; omega)

  have n5694 : n = 5694 := by 
    obtain ⟨j, k⟩ := h 
    obtain ⟨l, m⟩ := ta 
    have := m j 
    have := k l 
    linarith

  calc 
    n / 1000 + n % 1000 = 5694 / 1000 + 5694 % 1000 := by rw [n5694]
    _ = 699 := by norm_num