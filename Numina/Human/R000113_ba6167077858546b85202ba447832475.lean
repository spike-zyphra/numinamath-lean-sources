import Mathlib

open Finset Int Nat GCDMonoid

/-Theorem 3.6 states that if \( a \equiv b \mod m_1 \), \( a \equiv b \mod m_2 \), ..., \( a \equiv b \mod m_k \), where \( a, b, m_1, m_2, \ldots, m_k \) are integers and \( m_1, m_2, \ldots, m_k \) are positive integers, then it follows that
\[
a \equiv b \mod [m_1, m_2, \ldots, m_k]
\]
where \([m_1, m_2, \ldots, m_k]\) denotes the least common multiple of \( m_1, m_2, \ldots, m_k \).-/
theorem number_theory_4646 {a b : ℤ} {k : ℕ} {m : ℕ → ℤ}
                           (hpos : ∀ i ∈ Finset.range k, 0 < m i )
                           (hmod : ∀ i ∈ Finset.range k, a ≡ b [ZMOD m i])
                           : a ≡ b [ZMOD (lcm (image m (range k)) id)] := by
  -- We will prove this statement using mathematical induction on \( k \).
  induction k with
  | zero =>
    -- When \( k = 0 \), this statement is obviously true, because for any integers \( a \) and \( b \), we have \( a \equiv b \mod 1 \).
    simp [Int.modEq_one]
  | succ n h =>
    -- When \( k = n + 1 \), we assume by mathematical induction that the statement holds for any \( k = n \), and we need to prove that it also holds for \( k = n + 1 \).
    -- Since for any \( i \in \{0, 1, \ldots, n\} \), we have \( m_i > 0 \), it follows that for any \( i \in \{0, 1, \ldots, n-1\} \), \( m_i > 0 \).
    have hpos' : ∀ i ∈ Finset.range n, 0 < m i := by
      simp_all
      exact fun i hi => hpos i (Nat.lt_succ_of_lt hi)
    -- Similarly, for any \( i \in \{0, 1, \ldots, n-1\} \), we have \( a \equiv b \mod m_i \).
    have hmod' : ∀ i ∈ Finset.range n, a ≡ b [ZMOD m i] := by
      simp_all
      exact fun i hi => hmod i (Nat.lt_succ_of_lt hi)
    -- Therefore, we have \( a \equiv b \mod \text{lcm}[m_0, \ldots, m_{n-1}] \).
    have := h hpos' hmod'
    -- To prove the goal, we only need to show that \( \text{lcm}[m_0, \ldots, m_{n-1}, m_n] = \text{lcm}(\text{lcm}[m_0, \ldots, m_{n-1}], m_n) \).
    -- This is because if \( a \equiv b \mod x \) and \( a \equiv b \mod y \), then \( a \equiv b \mod \text{lcm}[x, y] \).
    suffices h : (image m (Finset.range (n + 1))).lcm id = GCDMonoid.lcm ((image m (Finset.range n)).lcm id) (m n) from by
      rw [h]
      apply Int.modEq_of_dvd
      apply @_root_.lcm_dvd
      · apply Int.ModEq.dvd this
      · apply Int.ModEq.dvd; aesop
    -- Thus, our goal transforms into proving that \( \text{lcm}[m_0, \ldots, m_{n-1}, m_n] = \text{lcm}[\text{lcm}[m_0, \ldots, m_{n-1}], m_n] \), and it is clear that these two numbers are equal.
    rw [range_succ,image_insert,lcm_insert,@_root_.lcm_comm]
    simp_all
    -- Therefore, our proof is complete.
