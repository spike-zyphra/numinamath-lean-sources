import Mathlib
/- Soit $a_{0}< a_{1}< a_{2}<\ldots$ une suite infinie d'entiers strictement positifs. Prouver qu'il existe un unique entier $n \geqslant 1$ tel que

$$
a_{n}<\frac{a_{0}+a_{1}+a_{2}+\cdots+a_{n}}{n} \leqslant a_{n+1} .
$$ -/
theorem number_theory_607657 (a : ℕ → ℤ) (ha : StrictMono a) (ha0 : 0 < a 0) (ha1 : 0 < a 1) (ha2 : 0 < a 2)
(han : ∀ n, 0 < a (n + 1)) : ∃! n, 1 ≤ n ∧ a n < (∑ i in Finset.range (n + 1), a i) / (n : ℝ) ∧ (∑ i in Finset.range (n + 1), a i) / (n : ℝ) ≤ a (n + 1):= by
  -- Define d(n) as the difference between the sum of first n+1 terms and n times a_n
  set d:= fun n => (∑ i in Finset.range (n + 1), a i) - n * a n with hd

  -- Prove that d(n+1) > d(n+2) for all n
  have h1 : ∀ n : ℕ, d (n + 1) > d (n + 2):= by
    intro n
    simp [hd]
    rw [show n + 1 + 1 = n + 2 by ring]
    rw [Finset.sum_range_succ]
    suffices (n + 1) * (a (n + 2) - a (n + 1)) > 0 by linarith
    simp [StrictMono] at ha
    specialize ha (show n + 1 < n + 2 by omega)
    replace ha : a (n + 2) - a (n + 1) > 0:= by linarith
    positivity

  -- Prove that there exists an n such that d(n+1) > 0 and d(n+2) ≤ 0
  have h2 : ∃ n : ℕ, d (n + 1) > 0 ∧ d (n + 2) ≤ 0:= by
    by_contra H
    simp at H
    -- Prove that d(1) > 0
    have h3 : d 1 > 0:= by
      simp [hd]
      rw [Finset.sum_range_succ]
      simp
      linarith
    -- If the statement is false, then d(n+1) > 0 for all n
    replace H : ∀ n : ℕ, d (n + 1) > 0:= by
      intro n
      induction n with
      | zero =>
        simp
        exact h3
      | succ n ih =>
        rw [show n + 1 + 1 = n + 2 by ring]
        exact H n ih
    -- But this leads to a contradiction with h1
    replace h1 : ∀ n : ℕ, d (n + 1) ≤ d 1 - n:= by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [show n + 1 + 1 = n + 2 by ring]
        specialize h1 n
        simp
        linarith
    specialize h1 ((d 1).natAbs)
    specialize H ((d 1).natAbs)
    simp at h1
    have g1 : |d 1| ≥ d 1:= by exact le_abs_self (d 1)
    linarith

  -- Extract the value of n from h2 and set m = n+1
  rcases h2 with ⟨n, hn1, hn2⟩
  set m:= n + 1 with hm
  clear_value m
  rw [show n + 2 = m + 1 by linarith] at hn2

  -- Prove that if a_n < (sum of a_0 through a_n)/n, then d(n) > 0
  have h2 : ∀ n : ℕ, n > 0 → ↑((a n) : ℝ) < ↑(∑ i ∈ Finset.range (n + 1), a i) / (↑n : ℝ) → d n > 0:= by
    intro n g1 g2
    rify at g1
    replace g2 : (↑(a n) : ℝ) * n < ↑(∑ i ∈ Finset.range (n + 1), a i) / (↑n : ℝ) * n:= by exact (mul_lt_mul_iff_of_pos_right g1).mpr g2
    rw [show ↑(∑ i ∈ Finset.range (n + 1), a i) / (↑n : ℝ) * n = ↑(∑ i ∈ Finset.range (n + 1), a i) by field_simp] at g2
    simp [hd]
    rify
    simp at g2
    linarith

  -- Prove that if (sum of a_0 through a_n)/n ≤ a_(n+1), then d(n+1) ≤ 0
  have h3 : ∀ n : ℕ, n > 0 → (↑(∑ i ∈ Finset.range (n + 1), a i) : ℝ) / ↑n ≤ ↑(a (n + 1)) → d (n + 1) ≤ 0:= by
    intro n g1 g2
    rify at g1
    replace g2 : (↑(∑ i ∈ Finset.range (n + 1), a i) : ℝ) ≤ ↑(a (n + 1)) * ↑n:= by exact (mul_inv_le_iff₀ g1).mp g2
    simp [hd]
    rw [Finset.sum_range_succ]
    rify
    simp at g2
    linarith

  -- Prove that m satisfies the required conditions and is unique
  simp [ExistsUnique]
  use m
  constructor
  .
    -- Prove that m satisfies the required conditions
    have g1 : m > 0:= by omega
    rify at g1
    refine ⟨(by omega), ?_, ?_⟩
    .
      -- Prove that a_m < (sum of a_0 through a_m)/m
      suffices (a m) * (↑m : ℝ) < (∑ x ∈ Finset.range (m + 1), ↑(a x)) by exact (lt_div_iff₀ g1).mpr this
      simp [hd] at hn1
      rify at hn1
      linarith
    .
      -- Prove that (sum of a_0 through a_m)/m ≤ a_(m+1)
      suffices (∑ x ∈ Finset.range (m + 1), ↑(a x)) ≤ ↑(a (m + 1)) * (↑m : ℝ) by exact (div_le_iff₀ g1).mpr this
      simp [hd] at hn2
      rw [Finset.sum_range_succ] at hn2
      rify at hn2
      linarith
  .
    -- Prove that m is unique
    intro y hy g1 g2
    specialize h2 y hy (by simp [g1])
    specialize h3 y hy (by simp [g2])
    clear g1 g2
    -- Prove that d decreases strictly
    replace h1 : ∀ i j : ℕ, d (i + j + 2) < d (i + 1):= by
      intro i j
      induction j with
      | zero =>
        simp
        exact h1 i
      | succ j ih =>
        rw [show i + (j + 1) + 2 = i + j + 3 by ring]
        specialize h1 (i + j + 1)
        rw [show i + j + 1 + 1 = i + j + 2 by ring] at h1
        rw [show i + j + 1 + 2 = i + j + 3 by ring] at h1
        linarith
    -- Prove that m+1 > y
    have g1 : m + 1 > y:= by
      by_contra H
      simp at H
      have g2 : m + 1 ≠ y:= by
        by_contra H1
        subst y
        linarith
      replace H : m + 1 < y:= by omega
      specialize h1 m (y - m - 2)
      rw [show m + (y - m - 2) + 2 = y by omega] at h1
      omega
    -- Prove that y+1 > m
    have g2 : y + 1 > m:= by
      by_contra H
      simp at H
      have g3 : y + 1 ≠ m:= by
        by_contra H1
        rw [H1] at h3
        linarith
      replace H : y + 1 < m:= by omega
      specialize h1 y (m - y - 2)
      rw [show y + (m - y - 2) + 2 = m by omega] at h1
      omega
    -- Conclude that y = m
    omega
