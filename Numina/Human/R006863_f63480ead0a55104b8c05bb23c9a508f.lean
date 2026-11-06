import Mathlib

/-Let $K$ be a positive integer. A three-digit number $n$, with first digit $d_1$, second digit $d_2$,
and third digit $d_3$ (so $n = 100d_1 + 10d_2 + d_3$), is said to have distinct digits if $d_1, d_2, d_3$ are all different,
$d_1 \neq 0$, $d_2, d_3 \in \{0, \dots, 9\}$.Such a number $n$ is $K$ times smaller than the sum of other numbers formed
by permuting its digits if $K \cdot n = S_{other}$. The sum $S_{other}$ includes all numbers formed
by permutations of $(d_1, d_2, d_3)$ different from $n$. If a permutation places $0$ in the leading position (e.g., $0 d_i d_j$),
that number is treated as a two-digit number (e.g., $10d_i + d_j$). There are $3!-1 = 5$ such "other" numbers.
The sum of $n$ and $S_{other}$ is $S_{all} = 222(d_1+d_2+d_3)$.
Let $K=2$. Determine all three-digit numbers $n$ with distinct digits,
which are $K$ times smaller than the sum of the other numbers written with the same digits.
Show that there are no such numbers.-/

theorem number_theory_641878: ¬ (∃ n: ℕ, ∃ d1 d2 d3, n = 100 * d1 + 10 * d2 + d3 ∧
  d1 ≠ 0 ∧ d1 ≤ 9 ∧ d2 ≤ 9 ∧ d3 ≤ 9 ∧ d2 ≠ d3 ∧ d1 ≠ d2 ∧ d1 ≠ d3 ∧
  2 * n = 222 * (d1 + d2 + d3) - n) := by
    by_contra! h
    obtain ⟨n, d1, d2, d3, hn, l1, l2, l3, l4, l5, l6, l7, l⟩ := h
    replace l: 3 * n = 222 * (d1 + d2 + d3) := by
      omega
    simp [hn] at l
    clear hn
    replace l: 26 * d1 = 64 * d2 + 73 * d3 := by
      omega
    have u: 2 ∣ d3 := by
      suffices 2 ∣ 73 * d3 by
        apply Nat.Coprime.dvd_of_dvd_mul_left at this
        tauto
        norm_num
      rw [show 73 * d3 = 64 * d2 + 73 * d3 - 64 * d2 by omega]
      apply Nat.dvd_sub
      .
        omega
      .
        rw [← l]
        omega
      .
        omega
    apply exists_eq_mul_right_of_dvd at u
    obtain ⟨a, u⟩ := u
    simp [u] at *
    replace l: 13 * d1 = 32 * d2 + 73 * a := by
      clear *- l
      omega
    have la: a < 2 := by
      nlinarith
    interval_cases a

    -- a = 0
    .
      simp at l l5 l7
      omega

    -- a = 1
    .
      simp at l l5 l7
      omega