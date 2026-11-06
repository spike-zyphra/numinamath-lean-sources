import Mathlib

/-- If the positive integer $n$ has positive integer divisors $a$ and $b$ with $n = ab$, then $a$
and $b$ are said to be $\textit{complementary}$ divisors of $n$. Suppose that $N$ is a positive
integer that has one complementary pair of divisors that differ by $20$ and another pair of
complementary divisors that differ by $23$. What is the sum of the digits of $N$?

$\textbf{(A) } 9 \qquad \textbf{(B) } 13\qquad \textbf{(C) } 15 \qquad \textbf{(D) } 17 \qquad
\textbf{(E) } 19$ -/
theorem number_theory_94369 {n : ℕ} (hn : n > 0)
    (h1 : ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ n = a * b ∧ |a - b| = 20)
    (h2 : ∃ c d : ℤ, c > 0 ∧ d > 0 ∧ n = c * d ∧ |c - d| = 23) :
    (Nat.digits 10 n).sum = 15 := by

  -- Let $a$ and $b$ be positive integers such that $n = a \cdot b$ and $|a - b| = 20$.
  rcases h1 with ⟨a, b, ha, hb, hnab, hab⟩

  -- Without loss of generality, assume that $a < b$.
  wlog hab2 : a < b generalizing a b
  · apply this b a hb ha
    · rw [hnab, mul_comm]
    · rw [abs_sub_comm, hab]
    · suffices a ≠ b by omega
      rintro rfl
      simp at hab

  -- Therefore, b = a + 20
  have hba : b = a + 20 := by
    suffices b - a = 20 by linarith
    calc _ = |b - a| := by symm; rw [abs_eq_self]; linarith
         _ = |a - b| := by rw [abs_sub_comm]
         _ = 20 := by assumption

  -- Let $c$ and $d$ be positive integers such that $n = c \cdot d$ and $|c - d| = 23$.
  rcases h2 with ⟨c, d, hc, hd, hncd, hcd⟩

  -- Without loss of generality, assume that $c < a$.
  wlog hca : c < a generalizing c d
  · apply this d c hd hc
    · rw [hncd, mul_comm]
    · rw [abs_sub_comm, hcd]
    · simp at hca
      by_contra! had

      by_cases hcd' : c < d
      · have : d = c + 23 := by
          suffices d - c = 23 by linarith
          calc _ = |d - c| := by symm; rw [abs_eq_self]; linarith
               _ = |c - d| := by rw [abs_sub_comm]
               _ = 23 := by assumption
        -- have : b < d := by linarith
        nlinarith
        -- suffices (n:ℤ) < n by linarith
        -- calc _ = a * b := by rw [hnab]
        --      _ < c * d := by nlinarith
        --       _ = n := by rw [hncd]
      · simp at hcd'
        have : c = d + 23 := by
          suffices c - d = 23 by linarith
          calc _ = |c - d| := by symm; rw [abs_eq_self]; linarith
               _ = 23 := by assumption
        nlinarith

  -- We can write $a = c + k$ for some positive integer $k$.
  let k := a - c
  have hkpos : k > 0 := by omega
  have hack : a = c + k := by omega

  -- Then, $d$ must be greater than $b$ because otherwise $c < a$ and $d ≤ b$ but they multiply to
  -- the same number $n$.
  have : b < d := by nlinarith

  -- And hence, $c < d$, so we can write $d = c + 23$.
  have hcd2 : d = c + 23 := by
    suffices d - c = 23 by linarith
    calc _ = |d - c| := by symm; rw [abs_eq_self]; linarith
         _ = |c - d| := by rw [abs_sub_comm]
         _ = 23 := by assumption

  -- In summary, we have the following inqualities:
  -- $c < a$ or equivalenty $0 < k$
  -- $b < d$ or equivalently $c + k + 20 = a + 20 < c + 23$ or equivalently $k < 3$
  have : k < 3 := by linarith

  -- So, $k = 1$ or $k = 2$.
  have : k = 1 ∨ k = 2 := by omega

  rcases this with (hk | hk); swap
  -- First, let's look at the $k = 2$ case. We will see that this case is impossible.
  · -- We have $n = c d = c (c + 23)$ and $n = a b = (c + 2) (c + 22)$
    have hnc1 : n = c * (c + 23) := by rw [hncd, hcd2]
    have hnc2 : n = (c + 2) * (c + 22) := by rw [hnab, hba, hack, hk]; ring

    -- Expanding out the parentheses,
    ring_nf at hnc1 hnc2
    -- And canceling the $n$'s, we get $c = -44$.
    have hc : c = -44 := by linarith
    -- But this is impossible.
    linarith

  -- Now, let's look at the $k = 1$ case.
  · -- We have $n = c d = c (c + 23)$ and $n = a b = (c + 1) (c + 21)$
    have hnc1 : n = c * (c + 23) := by rw [hncd, hcd2]
    have hnc2 : n = (c + 1) * (c + 21) := by rw [hnab, hba, hack, hk]; ring

    -- Expanding out the parentheses,
    ring_nf at hnc1 hnc2
    -- And canceling the $n$'s, we get $c = 21$.
    have hc : c = 21 := by linarith

    -- Then, $n = 21 \cdot 44 = 924$.
    have hn : n = 924 := by
      zify
      rw [hnc1, hc]
      norm_num

    -- The sum of the digits of $924$ is $15$ as required.
    simp [hn]