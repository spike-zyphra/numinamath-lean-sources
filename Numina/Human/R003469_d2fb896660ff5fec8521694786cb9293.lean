import Mathlib

/- # Problem:
 \section*{Problem 3 - 121033}

Imagine all prime numbers, starting with the prime number 5, numbered in ascending order; thus numbered are:

\begin{tabular}{lccccccc}
Prime & 5 & 7 & 11 & 13 & 17 & 19 & \(\ldots\) \\
Number & 1 & 2 & 3 & 4 & 5 & 6 & \(\ldots\)
\end{tabular}

It is to be proven that then every prime number is greater than three times its number.
 -/
theorem number_theory_185793 : (n : ℕ) → Nat.nth (fun n => n.Prime ∧ n ≥ 5) n ≥ 3 * (n + 1)
  -- The statement is clearly true for the prime numbers with numbers (in this list) 1 and 2, i.e., 5 and 7.
  | 0 => by
    set P := fun n ↦ Nat.Prime n ∧ n ≥ 5
    suffices Nat.nth P 0 = 5 by
      linarith
    have : P 5 := by
      decide
    have := Nat.nth_count this
    exact this
  | 1 => by
    -- adapted from above by Copilot
    set P := fun n ↦ Nat.Prime n ∧ n ≥ 5
    suffices Nat.nth P 1 = 7 by
      linarith
    have : P 7 := by
      decide
    have := Nat.nth_count this
    exact this
  | n + 2 => by
    set P := fun n ↦ Nat.Prime n ∧ n ≥ 5
    -- If it also holds for the prime number with number (in this list) \(k\) for a positive integer \(k\), then we now show that it also holds for the one with number \(k+2\), thus proving it inductively for all prime numbers \(\geq 5\).
    have ih_n := number_theory_185793 n
    -- So let \(p\) be the prime number with number \(k\), and let \(p > 3 k\).
    set p := Nat.nth P n
    /-
    Since \(p > 2\) is odd, \(p+1, p+3\) and \(p+5\) cannot be prime numbers.

    Furthermore, of the three consecutive odd numbers \(p, p+2\) and \(p+4\), one is divisible by three. Since \(p > 3\) is not, in addition to the three even numbers mentioned, at least one of the two odd numbers between \(p+1\) and \(p+5\) is not a prime number. Therefore, after \(p\), there can be at most one more prime number that is \(\leq p+5\).

    Consequently, the next largest prime number - i.e., the one with number \(k+2\) - has at least the value \(p+6 > 3 k+6=3(k+2)\), which was to be proven.
     -/
    suffices Nat.nth P (n + 2) ≥ p + 6 by
      linarith
    have setOf_P_infinite : (setOf P).Infinite := by
      --simp [P]
      have : setOf P = {p | Nat.Prime p} \ Set.Ico 0 5 := by
        ext p
        simp [P]
      rw [this]
      --have := Nat.Primes.infinite
      have infinite_setOf_prime := Nat.infinite_setOf_prime
      have finite_ico : (Set.Ico 0 5).Finite := by
        exact Set.finite_Ico 0 5
      exact Set.Infinite.diff infinite_setOf_prime finite_ico
    suffices Nat.count P (p + 6) ≤ n + 2 by
      exact (Nat.count_le_iff_le_nth setOf_P_infinite).mp this
    suffices Nat.count P (p + 6) ≤ n + 2 by
      linarith
    rw [Nat.count_add P p 6]
    have : Nat.count P p = n := by
      exact Nat.count_nth_of_infinite setOf_P_infinite n
    rw [this]
    suffices Nat.count (fun k ↦ P (p + k)) 6 ≤ 2 by
      linarith
    rw [Nat.count_eq_card_filter_range]
    --simp [P]
    --set Q := fun k ↦ P (p + k)
    let Q k := P (p + k)
    change ((Finset.range 6).filter Q).card ≤ 2
    --set s := (Finset.range 6).filter Q
    let even : Finset ℕ := {0, 2, 4}
    let odd : Finset ℕ := {1, 3, 5}
    have : Finset.range 6 = even ∪ odd := by
      decide
    rw [this]
    have : (even ∪ odd).filter Q = even.filter Q ∪ odd.filter Q := by
      exact Finset.filter_union Q even odd
    rw [this]
    have : P p := by
      unfold p
      --exact? -- strange, `exact?` doesn't find the solution below.
      exact Nat.nth_mem_of_infinite setOf_P_infinite n
    simp [P] at this
    rcases this with ⟨prime_p, _5_le_p⟩
    have : odd.filter Q = ∅ := by
      ext k
      simp [P, Q]
      intro k_mem_odd prime_p_add_k
      exfalso
      have : k % 2 = 1 := by
        fin_cases k_mem_odd <;>
        . rfl
      have : p % 2 = 1 := by
        suffices Odd p by
          exact Nat.odd_iff.mp this
        apply Nat.Prime.odd_of_ne_two
        . exact prime_p
        . linarith
      have : 2 ∣ p + k := by
        omega
      have : (p + k) % 2 = 1 := by
        apply Nat.odd_iff.mp
        apply Nat.Prime.odd_of_ne_two prime_p_add_k
        . linarith
      omega
    simp [this]
    have : (even.filter Q).card ≤ 2 := by
      have : ∃ k ∈ even, ¬ Q k := by
        simp [Q, P]
        have : ∃ k ∈ even, 3 ∣ p + k := by
          simp [even]
          omega
          --mod_cases p % 3
        rcases this with ⟨k, k_mem_even, _3_dvd_p_add_k⟩
        use k, k_mem_even
        intro prime_p_add_k
        exfalso
        have : p + k ≥ 5 := by
          linarith
        rcases _3_dvd_p_add_k with ⟨c, p_add_k_eq_3_c⟩
        rw [p_add_k_eq_3_c] at prime_p_add_k
        revert prime_p_add_k
        simp
        refine Nat.not_prime_mul ?_ ?_
        . omega
        . omega
      rcases this with ⟨k, k_mem_even, not_Q_k⟩
      have : even.filter Q ⊆ even.erase k := by
        intro k' k'_mem_even_filter_Q
        simp
        constructor
        . rintro rfl
          apply not_Q_k
          simp at k'_mem_even_filter_Q
          exact k'_mem_even_filter_Q.2
        . exact Finset.mem_of_mem_filter k' k'_mem_even_filter_Q
      have : (even.filter Q).card ≤ (even.erase k).card := by
        exact Finset.card_le_card this
      have : (even.erase k).card = 2 := by
        have : even.card = 3 := by
          simp [even]
        have : even.card = (even.erase k).card + 1 := by
          exact Eq.symm (Finset.card_erase_add_one k_mem_even)
        linarith
      linarith
    exact this
