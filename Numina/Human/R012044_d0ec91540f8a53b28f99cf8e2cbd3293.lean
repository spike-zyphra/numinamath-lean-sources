import Mathlib

def f: ℕ → ℤ
  | 1 => 11
  | 2 => 15
  | 3 => 7
  | 4 => 8
  | 5 => 4
  | 6 => 13
  | _ => 0

/-Frank has two integers that add up to 26.
Kees adds two more integers and gets 41.
Pieter adds two more integers and gets 58.
At least how many of the six added numbers are even?
A) 0 B) 1 C) 2 D) 3 E) 4-/

theorem number_theory_175779: IsLeast {k: ℕ | ∃ a: ℕ → ℤ, a 1 + a 2 = 26 ∧ 26 + a 3 + a 4 = 41 ∧
  41 + a 5 + a 6 = 58 ∧ k = {i: ℕ | 1 ≤ i ∧ i ≤ 6 ∧ Even (a i)}.encard} 2 := by

  constructor

  -- show 2 is true
  .
    simp
    use f
    constructor
    .
      simp [f]
    .
      constructor
      .
        simp [f]
      .
        constructor
        .
          simp [f]
        .
          have h_eq: {i | 1 ≤ i ∧ i ≤ 6 ∧ Even (f i)} = {4 , 5} := by
            ext i
            constructor
            .
              intro h
              simp at h
              rcases h with ⟨h1, h2, h3⟩
              simp
              interval_cases i
              all_goals simp [f] at h3; try omega
              all_goals absurd h3; simp; decide
            .
              intro h
              simp at h
              rcases h with h | h
              .
                simp [h, f]
                decide
              .
                simp [h, f]
                decide

          rw [h_eq]
          simp [Set.encard]

  -- show 2 is least
  .
    intro k
    intro h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨a, h1, h2, h3, h4⟩ := h
    by_contra! l
    replace l: k ≤ 1:= by omega
    replace l: k ≤ (1: ℕ∞) := by
      norm_cast
    rw [h4] at l
    clear h4
    rw [Set.encard_le_one_iff] at l
    absurd l
    simp
    replace h2: a 3 + a 4 = 15 := by omega
    replace h3: a 5 + a 6 = 17 := by omega

    -- then a 3 ∨ a 4 is Even
    have o1: Even (a 3) ∨ Even (a 4) := by
      by_contra! s
      simp at s
      have o: Even (15: ℤ) := by
        rw [← h2]
        rw [Int.even_add']
        simp [s]
      absurd o
      simp
      decide

    -- then a 5 ∨ a 6 is Even
    have o2: Even (a 5) ∨ Even (a 6) := by
      by_contra! s
      simp at s
      have o: Even (17: ℤ) := by
        rw [← h3]
        rw [Int.even_add']
        simp [s]
      absurd o
      simp
      decide

    rcases o1 with o1 | o1
    .
      rcases o2 with o2 | o2
      .
        use 3
        norm_num
        simp [o1]
        use 5
        norm_num
        simp [o2]
      .
        use 3
        norm_num
        simp [o1]
        use 6
        norm_num
        simp [o2]

    .
      rcases o2 with o2 | o2
      .
        use 4
        norm_num
        simp [o1]
        use 5
        norm_num
        simp [o2]
      .
        use 4
        norm_num
        simp [o1]
        use 6
        norm_num
        simp [o2]