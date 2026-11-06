import Mathlib

/-Suppose that $n$ is a positive integer such that in base $7$, then $n$ can be expressed as $\overline{ABC}_7$, and in base $11$, then $n$ can be expressed as $\overline{CBA}_{11}$. Find the largest possible value of $n$ in base $10$.-/
theorem number_theory_15780 :
    IsGreatest {n > 0 | ∃(A B C : ℕ), A < 7 ∧ B < 7 ∧ C < 7 ∧ Nat.digits 7 n = [C, B, A] ∧ Nat.digits 11 n = [A, B, C]} 247 := by
    -- n ≤ 247 ∧ ((Nat.digits 11 247).reverse = (Nat.digits 7 247)) := by
  -- We convert $n$ to base $10$.
  constructor
  · -- Prove that 247 is in the set.
    simp
    use 5
    simp
    use 0
    simp
  . -- Prove that 247 is the greatest element in the set.
    apply mem_upperBounds.mpr
    simp
    intro n hn A hA B hB C hC h7 h11
    -- The base $7$ expression implies that $n = 49A + 7B + C$,
    have h7 : n = A * 49 + B * 7 + C := by
      have : n = Nat.ofDigits 7 [C, B, A] := by
        rw [h7.symm, Eq.comm]
        exact Nat.ofDigits_digits 7 n
      rw [this, Nat.ofDigits_eq_foldr]
      simp
      linarith
    -- and the base $11$ expression implies that $n = 121C + 11B + A$.
    have h11 : n = C * 121 + B * 11 + A := by
      have : n = Nat.ofDigits 11 [A, B, C] := by
        rw [h11.symm, Eq.comm]
        exact Nat.ofDigits_digits 11 n
      rw [this, Nat.ofDigits_eq_foldr]
      simp
      linarith
    -- Setting the two expressions equal to each other yields that $$n = 49A + 7B + C = 121C + 11B + A \Longrightarrow 48A - 4B - 120C = 0.$$
    have hd: 48 * A - 4 * B - 120 * C = 0 := by omega
    -- Isolating $B$, we get $$B = \frac{48A - 120C}{4} = 12A - 30C = 6(2A - 5C).$$
    have hB' : B = 6 * (2 * A - 5 * C) := by omega
    -- It follows that $B$ is divisible by $6$, and since $B$ is a base $7$ digit, then $B$ is either $0$ or $6$.
    obtain (h | h) := show B = 0 ∨ B = 6 by omega
    . -- If $B$ is equal to $0$, then $2A - 5C = 0 \Longrightarrow 2A = 5C$, so $A$ must be divisible by $5$ and hence must be either $0$ or $5$.
      rw [h] at hB'
      simp at hB'
      -- Since $n$ is a three-digit number in base $7$, then $A \neq 0$, so $A = 5$
      have hA' : A = 5 := by omega
      -- and $C = 2$. Thus, $n = 502_7 = 5 \cdot 7^2 + 2 = 247$.
      have hC' : C = 2 := by omega
      rw [hA', h, hC'] at h7
      linarith
    . -- If $B$ is equal to $6$, then $2A - 5C = 1$, so $2A - 1 = 5C$ and $2A - 1$ must be divisible by 5.
      rw [h] at hB'
      simp at hB'
      -- Since $A$ is a base $7$ digit, it follows that $A = 3$ and $C = 1$.
      have hA' : A = 3 := by omega
      have hC' : C = 1 := by omega
      rw [hA', h, hC'] at h7
      -- so, n = 190 < 247.
      linarith
