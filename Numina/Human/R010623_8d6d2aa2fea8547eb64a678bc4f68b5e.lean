import Mathlib

/-How many two-digit prime numbers have the property that both digits are also primes?-/

theorem number_theory_609302:
{x: ℕ | 10 ≤ x ∧ x ≤ 99 ∧ Nat.Prime x ∧ Nat.Prime (x % 10) ∧ Nat.Prime (x / 10)}.encard = 4 := by

  -- we compute the set directly
  have h_eq: {x: ℕ | 10 ≤ x ∧ x ≤ 99 ∧ Nat.Prime x ∧ Nat.Prime (x % 10) ∧ Nat.Prime (x / 10)}
  = {23, 37, 53, 73} := by
    ext x
    constructor
    -- the forward direction
    . intro h
      simp at h
      simp
      rcases h with ⟨hx1,hx2,h1,h2,h3⟩
      let a:= x % 10
      have ha: x % 10 = a := by rfl
      let b:= x / 10
      have hb: x / 10 = b := by rfl
      have hx: x = 10 * b + a := by omega
      rw [ha] at h2
      rw [hb] at h3
      rw [hx]
      rw [hx] at h1
      have ha1: 0 ≤ a := by omega
      have ha2: a ≤ 9 := by omega
      clear ha
      have hb1: 1 ≤ b := by omega
      have hb2: b ≤ 9 := by omega
      clear hb hx hx1 hx2
      clear_value a b
      have b_val: b = 2 ∨ b = 3 ∨ b = 5 ∨ b = 7 := by
        interval_cases b
        all_goals try omega
        all_goals absurd h3; norm_num
      clear hb1 hb2 h3
      rcases b_val with h | h | h | h
      -- b = 2
      . simp [h] at *
        clear ha1 h
        interval_cases a
        all_goals
          try omega
        all_goals
          absurd h1
          norm_num
        all_goals
          absurd h2
          norm_num
      -- b = 3
      . simp [h] at *
        clear ha1 h
        interval_cases a
        all_goals
          try omega
        all_goals
          absurd h1
          norm_num
        all_goals
          absurd h2
          norm_num
      -- b = 5
      . simp [h] at *
        clear ha1 h
        interval_cases a
        all_goals
          try omega
        all_goals
          absurd h1
          norm_num
        all_goals
          absurd h2
          norm_num
      -- b = 7
      . simp [h] at *
        clear ha1 h
        interval_cases a
        all_goals
          try omega
        all_goals
          absurd h1
          norm_num
        all_goals
          absurd h2
          norm_num

    -- the backward direction
    . intro h
      simp at h
      rcases h with h | h | h | h
      all_goals
         simp [h]
         norm_num

  -- Then compute the cardinality
  rw [h_eq]
  simp [Set.encard]