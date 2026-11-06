import Mathlib

/-Let $N$ be a five-digit number with digits $d_4 d_3 d_2 d_1 d_0$ (so $N = 10000 d_4 + 1000 d_3 + 100 d_2 + 10 d_1 + d_0$).
Suppose that when $N$ is multiplied by $k_0=4$, the result is a five-digit number with the same digits but in reverse order
(i.e., $4N = 10000 d_0 + 1000 d_1 + 100 d_2 + 10 d_3 + d_4$). Find the number $N$. Show the answer is $21978$.-/

theorem number_theory_637057 (N d4 d3 d2 d1 d0: ℤ)
  (h0: 1 ≤ d4 ∧ d4 ≤ 9 ∧ 0 ≤ d3 ∧ d3 ≤ 9 ∧ 0 ≤ d2 ∧ d2 ≤ 9 ∧ 0 ≤ d1 ∧ d1 ≤ 9 ∧ 0 ≤ d0 ∧ d0 ≤ 9)
  (h1: N = 10000 * d4 + 1000 * d3 + 100 * d2 + 10 * d1 + d0) (h2: 4 * N = 10000 * d0 + 1000 * d1 + 100 * d2 + 10 * d3 + d4):
    N = 21978 := by

  rcases h0 with ⟨l4, r4, l3, r3, l2, r2, l1, r1, l0, r0⟩
  simp [h1] at h2
  rw [h1]
  clear h1
  have v4: d4 = 2 := by omega
  simp [v4] at *
  have v3: d3 = 1 := by omega
  simp [v3] at *
  have v0: d0 = 8 := by omega
  simp [v0] at *
  suffices d2 = 9 ∧ d1 = 7 by simp [this]
  replace h2: 5 * d2 + 67 = 16 * d1 := by
    nlinarith
  have ld4: 5 ≤ d1 := by omega
  interval_cases d1
  all_goals omega