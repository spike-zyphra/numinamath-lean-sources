import Mathlib

/-Let $n$ be a natural number such that $n$ is a 4-digit number (i.e., $1000 \le n \le 9999$).
Let $n'$ be the integer obtained by writing the decimal digits of $n$ in reverse order. If the sum $n+n'$ is equal to $1001$,
then $n$ must be $1000$.-/

theorem number_theory_638209 (n n': ℤ) (h: ∃ a b c d, 1 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c ≤ 9 ∧
  0 ≤ d ∧ d ≤ 9 ∧ n = a * 1000 + b * 100 + c * 10 + d ∧ n' = d * 1000 + c * 100 + b * 10 + a) (h2: n + n' = 1001): n = 1000 := by

  rcases h with ⟨a, b, c, d, ha1, ha2, hb1, hb2, hc1, hc2, hd1, hd2, hn, hn'⟩

  -- we show that a = 1 firstly
  have va: a = 1 := by
    rw [hn'] at h2
    clear hn'
    omega

  simp [va] at *

  -- then we show that b = 0
  have vb: b = 0 := by
    rw [hn'] at h2
    clear hn'
    omega

  simp [vb] at *

  -- then we show that c = 0
  have vc: c = 0 := by
    rw [hn'] at h2
    clear hn'
    omega

  simp [vc] at *

  -- finally we show that d = 0
  have vd: d = 0 := by
    rw [hn'] at h2
    clear hn'
    omega

  simp [vd] at *
  tauto