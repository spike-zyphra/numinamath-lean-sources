import Mathlib
/- 14. (7th Balkan Mathematical Olympiad, 1990) Let $a_{1}=1, a_{2}=3$, and for all positive integers $n$,
$$
a_{n+2}=(n+3) a_{n+1}-(n+2) a_{n} \text {. }
$$

Find all values of $n$ for which $a_{n}$ is divisible by 11. -/
theorem algebra_110851 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 3) (han : ∀ n > 0, a (n + 2) = (n + 3) * a (n + 1) - (n + 2) * a n) : {n | 1 ≤ n ∧ 11 ∣ a n} = {4, 8} ∪ {n | 10 ≤ n} := by
  ext n
  -- Prove by induction that a(n+1) equals the sum of factorials from 1! to (n+1)!
  have h : ∀ n : ℕ, (a (n + 1) = ∑ i ∈ Finset.range (n + 1), Nat.factorial (i + 1)) ∧ (a (n + 2) = ∑ i ∈ Finset.range (n + 2), Nat.factorial (i + 1)):= by
    intro n
    induction n with
    -- Base case: n = 0
    | zero =>
      simp
      rw [ha1, ha2]
      rw [Finset.sum_range_succ]
      simp
    -- Inductive step: n → n+1
    | succ n ih =>
      rcases ih with ⟨ih1, ih2⟩
      constructor
      .
        rw [show n + 1 + 1 = n + 2 by ring_nf]
        rw [ih2]
      .
        rw [show n + 2 + 1 = n + 3 by ring_nf]
        specialize han (n + 1) (by linarith)
        rw [show n + 1 + 2 = n + 3 by ring_nf] at han
        simp at han
        rw [show n + 1 + 1 = n + 2 by ring_nf] at han
        rw [show (↑n : ℤ) + 1 + 3 = n + 4 by ring_nf] at han
        rw [show (↑n : ℤ) + 1 + 2 = n + 3 by ring_nf] at han
        -- Prove that a(n+2) - a(n+1) = (n+2)!
        have g1 : a (n + 2) - a (n + 1) = (n + 2).factorial:= by
          rw [ih2]
          rw [show n + 2 = n + 1 + 1 by ring_nf]
          rw [Finset.sum_range_succ]
          simp
          rw [ih1]
          simp
        rw [show ((↑n : ℤ) + 4) * a (n + 2) - (↑n + 3) * a (n + 1) = a (n + 2) + (n + 3) * (a (n + 2) - a (n + 1)) by linarith] at han
        rw [show n + 3 = n + 2 + 1 by ring_nf] at han
        rw [Finset.sum_range_succ]
        rw [han, g1, ih2]
        simp
        rw [show (↑n : ℤ) + 3 = n + 2 + 1 by ring_nf]
        suffices (n + 2 + 1) * (n + 2).factorial = (n + 2 + 1).factorial by zify at this ; exact this
        exact rfl
  -- Simplify the formula for a(n+1)
  replace h : ∀ n : ℕ, a (n + 1) = ↑(∑ i ∈ Finset.range (n + 1), (i + 1).factorial):= by
    intro n
    exact (h n).1
  -- Prove that 11 divides (n+11)! for all n
  have h3 : ∀ n : ℕ, 11 ∣ (n + 11).factorial:= by
    intro n
    induction n with
    | zero =>
      simp
      rw [Nat.factorial_succ]
      simp
    | succ n ih =>
      rw [show n + 1 + 11 = n + 11 + 1 by ring_nf]
      rw [Nat.factorial_succ]
      rw [show n + 11 + 1 = n + 12 by ring_nf]
      set t:= (n + 11).factorial
      clear_value t
      exact Dvd.dvd.mul_left ih (n + 12)
  -- Prove that if 11 divides a(n+10), then 11 divides a(n+11)
  have h4 : ∀ n : ℕ, 11 ∣ a (n + 10) → 11 ∣ a (n + 11):= by
    intro n hn
    have g1:= h (n + 10)
    have g2:= h (n + 9)
    rw [Finset.sum_range_succ] at g1
    rw [show n + 10 + 1 = n + 11 by ring_nf] at g1
    rw [show n + 9 + 1 = n + 10 by ring_nf] at g2
    simp at g1 g2
    rw [←g2] at g1
    rw [g1]
    specialize h3 n
    zify at h3
    exact (Int.dvd_add_right hn).mpr h3
  -- Prove that 11 divides a(n+10) for all n
  replace h4 : ∀ n : ℕ, 11 ∣ a (n + 10):= by
    intro n
    induction n with
    | zero =>
      simp
      specialize h 9
      rw [show 9 + 1 = 10 by ring_nf] at h
      rw [h]
      simp
      suffices 11 ∣ ∑ x ∈ Finset.range 10, (x + 1).factorial by zify at this ; exact this
      repeat rw [Finset.sum_range_succ]
      repeat rw [Nat.factorial_succ]
      simp
      omega
    | succ n ih =>
      rw [show n + 1 + 10 = n + 11 by ring_nf]
      exact h4 n ih
  -- Prove the forward direction: if 11 divides a_n, then n ∈ {4, 8} ∪ {n | n ≥ 10}
  constructor
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    by_cases hn : n ≥ 10
    .
      simp
      right
      exact hn
    .
      simp at hn
      by_cases hn1 : n = 4
      .
        subst n
        simp
      .
        by_cases hn2 : n = 8
        .
          subst n
          simp
        .
          replace hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 9:= by omega
          rcases hn with hn | hn | hn | hn | hn | hn | hn
          all_goals
            subst n
            rw [h _] at h2
            repeat rw [Finset.sum_range_succ] at h2
          .
            simp at h2
            omega
          .
            simp at h2
            omega
          all_goals
            repeat rw [Nat.factorial_succ] at h2
            simp at h2
            omega
  -- Prove the backward direction: if n ∈ {4, 8} ∪ {n | n ≥ 10}, then 11 divides a_n
  .
    intro h
    simp at h
    rcases h with h | h
    .
      rcases h with h | h
      all_goals
        subst n
        simp
        rw [h _]
        simp
        repeat rw [Finset.sum_range_succ]
        repeat rw [Nat.factorial_succ]
        simp
        omega
    .
      simp
      refine ⟨(by omega), ?_⟩
      specialize h4 (n - 10)
      rw [show n - 10 + 10 = n by omega] at h4
      exact h4
