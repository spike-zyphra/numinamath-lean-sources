import Mathlib
/-- Let $N$ be the greatest four-digit positive integer with the property that whenever one of its digits is changed to $1$, the resulting number is divisible by $7$. Let $Q$ and $R$ be the quotient and remainder, respectively, when $N$ is divided by $1000$. Find $Q+R$. -/
theorem number_theory_93319 (n : ℕ) (h : IsGreatest {n | ∃ (a b c d : ℕ), 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ 7 ∣ 1000 + 100 * b + 10 * c + d ∧ 7 ∣ 1000 * a + 100 + 10 * c + d ∧ 7 ∣ 1000 * a + 100 * b + 10 + d ∧ 7 ∣ 1000 * a + 100 * b + 10 * c + 1} n) : n / 1000 + n % 1000 = 699 := by
  have ta : IsGreatest {n | ∃ (a b c d : ℕ), 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ 7 ∣ 1000 + 100 * b + 10 * c + d ∧ 7 ∣ 1000 * a + 100 + 10 * c + d ∧ 7 ∣ 1000 * a + 100 * b + 10 + d ∧ 7 ∣ 1000 * a + 100 * b + 10 * c + 1} 5694 := by
    clear n h -- distraction
    constructor
    -- witness
    · exists 5, 6, 9, 4
    -- optimality
    · intros n hn
      obtain ⟨a, b, c, d, hn, hh, ha, hb, hc, hd, s1, s2, s3, s4⟩ := hn
      by_cases u : n ≤ 5694
      · exact u
      have v : 5695 ≤ n := by linarith
      clear u
      /-
      Reducing, we get
      $6+2b+3c+d \equiv 0 \pmod{7}$ $(1)$
      $6a+2+3c+d \equiv 0 \pmod{7}$ $(2)$
      $6a+2b+3+d \equiv 0 \pmod{7}$ $(3)$
      $6a+2b+3c+1 \equiv 0 \pmod{7}$ $(4)$
      -/
      have q1 : 7 ∣ 6 + 2 * b + 3 * c + d := by clear * - s1; omega
      have q2 : 7 ∣ 6 * a + 2 + 3 * c + d := by clear * - s2; omega
      have q3 : 7 ∣ 6 * a + 2 * b + 3 + d := by clear * - s3; omega
      have q4 : 7 ∣ 6 * a + 2 * b + 3 * c + 1 := by clear * - s4; omega
      zify at q1 q2 q3 q4
      -- Subtracting $(2)-(1), (3)-(2), (4)-(3), (4)-(1)$, we get:
      have d1 := Int.dvd_sub q2 q1
      have d2 := Int.dvd_sub q3 q2
      have d3 := Int.dvd_sub q4 q3
      have d4 := Int.dvd_sub q4 q1
      ring_nf at d1 d2 d3 d4
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 5 := by clear * - hn hh; omega
      -- clear off all n < 5
      all_goals try (clear * - hd v hh ha hb hc; omega)
      -- clear off remaining goals
      all_goals (ring_nf at *; omega)

  have tb : n = 5694 := by
    obtain ⟨j, k⟩ := h
    obtain ⟨l, m⟩ := ta
    have := m j
    have r := k l
    linarith
  subst n
  norm_num