import Mathlib

/-In the set of positive integers, the largest odd number that
cannot be written as the sum of three unequal composite numbers is .-/

theorem number_theory_627826: IsGreatest {n | Odd n ∧ ¬ ∃ c1 c2 c3 : ℕ,
1 < c1 ∧ c1 < c2 ∧ c2 < c3 ∧ ¬ Nat.Prime c1 ∧ ¬ Nat.Prime c2 ∧ ¬ Nat.Prime c3 ∧ n = c1 + c2 + c3} 17 := by
  constructor

  -- the forward direction
  .
    simp only [Set.mem_setOf_eq]
    constructor
    .
      decide
    .
      by_contra! h
      obtain ⟨c1, c2, c3, l1, l2, l3, p1, p2, p3, h⟩ := h
      have s1: c1 ≤ 5 := by omega

      -- then c1 = 4
      have f1: c1 = 4 := by
        interval_cases c1
        all_goals norm_num at p1
        omega

      simp [f1] at *
      replace h: c2 + c3 = 13 := by
        omega
      have s2: c2 ≤ 6 := by omega
      interval_cases c2
      .
        norm_num at p2
      .
        replace h: c3 = 7 := by omega
        simp [h] at p3
        norm_num at p3


  -- the backward direction
  .
    intro n h
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨hn, h⟩
    by_contra! l
    absurd h

    -- we use n = 4 + 9 + (n - 13)
    by_cases u: n < 22

    -- case n < 22, we use 4 + (n - 13) + 9
    .
      use 4, (n - 13), 9
      norm_num
      constructor
      .
        omega
      .
        constructor
        .
          omega
        .
          constructor
          .
            by_contra! f
            have c:= Nat.Prime.odd_of_ne_two f (by omega)
            absurd hn
            simp
            rw [show n = n - 13 + 13 by omega]
            rw [Nat.even_add']
            simp [c]
            decide
          .
            omega

    -- case n ≥ 22, we use 4 + 9 + (n - 13)
    .
      use 4, 9, (n - 13)
      norm_num
      simp at u
      clear l
      constructor
      .
        suffices n ≠ 22 by omega
        by_contra! f
        simp [f] at hn
        absurd hn
        decide
      .
        constructor
        .
          by_contra! f
          have c:= Nat.Prime.odd_of_ne_two f (by omega)
          absurd hn
          simp
          rw [show n = n - 13 + 13 by omega]
          rw [Nat.even_add']
          simp [c]
          decide
        .
          omega