import Mathlib

/-Let $M$ be a positive integer. An eight-digit natural number $A$ is obtained
from an eight-digit number $B$ by swapping the last digit of $B$ to the first place.
(This means that if $B = 10x + d_0$ where $d_0$ is the last digit of $B$, then $A = d_0 \cdot 10^7 + x$.)
It is known that $B$ is coprime with $M$ and $B > 44444444$. If $M=10$, find the largest and smallest numbers $A$
that satisfy these conditions. Show that the smallest $A$ is $14444445$ and the largest $A$ is $99999999$.
-/

theorem number_theory_639011: IsLeast {A: ℕ | ∃ B x d, d < 10 ∧ 10^6 ≤ x ∧ x < 10^7 ∧ B = 10 * x + d
  ∧ 44444444 < B ∧ Nat.Coprime B 10 ∧ A = d * 10^7 + x} 14444445 ∧
  IsGreatest {A: ℕ | ∃ B x d, d < 10 ∧ 10^6 ≤ x ∧ x < 10^7 ∧ B = 10 * x + d
  ∧ 44444444 < B ∧ Nat.Coprime B 10 ∧ A = d * 10^7 + x} 99999999 := by

  constructor

  -- the least side
  .
    constructor

    -- show 14444445 is in the set
    .
      simp
      use 44444451
      use 4444445, 1
      norm_num
    .
    -- show that 14444445 is the least
      intros A h
      simp at h
      obtain ⟨B, x, d, h1, h2, h3, h4, h5, h6, h7⟩ := h
      have ld: 1 ≤ d := by
        by_contra! o
        replace o: d = 0 := by omega
        simp [o] at h4
        rw [h4] at h6
        absurd h6
        have f1: 10 ∣ 10 * x := by
          simp
        have f2: 10 ∣ 10 := by
          simp
        have f3: 1 < 10 := by
          omega
        apply Nat.not_coprime_of_dvd_of_dvd f3 f1 f2
      rw [h7]
      by_cases r: d = 1
      .
        simp [r] at *
        suffices 4444444 < x by
          omega
        by_contra! o
        rw [h4] at h5
        clear *- h5 o
        omega
      .
        replace r: 2 ≤ d := by omega
        clear * - r
        omega


  -- the greatest side
  .
    constructor

    -- show 99999999 is in the set
    .
      simp
      use 99999999
      use 9999999, 9
      norm_num
    .
    -- show that 99999999 is the greatest
      intros A h
      simp at h
      obtain ⟨B, x, d, h1, h2, h3, h4, h5, h6, h7⟩ := h
      rw [h7]
      omega