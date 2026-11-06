import Mathlib

/-
Show that the integer 12 has no primitive roots.
-/
theorem number_theory_4993
    (has_primitive_root : ℕ → Prop)
    (h_hpr : ∀ x, has_primitive_root x = (
      (x = 2) ∨ (x = 4) ∨
      (∃ p k, p.Prime ∧ Odd p ∧ k > 0 ∧ x = p ^ k) ∨
      (∃ p k, p.Prime ∧ Odd p ∧ k > 0 ∧ x = 2 * p ^ k)))
    : ¬ has_primitive_root 12 := by
  simp only [h_hpr, not_or, not_exists]
  have r1 : ¬ 12 = 2 := by norm_num
  have r2 : ¬ 12 = 4 := by norm_num
  have r3 : ∀ p k , ¬ (p.Prime ∧ Odd p ∧ k > 0 ∧ 12 = p ^ k) := by
    simp only [not_and]
    rintro p k h_pp h_op h_kpos
    have h_knezero : ¬ k = 0 := Nat.not_eq_zero_of_lt h_kpos
    by_cases h1 : p ≤ 12
    -- p ≤ 12
    . rcases (le_or_gt p 1) with h2 | h2
      -- p = 0, 1, interval_cases p
      . interval_cases p
        all_goals simp [h_knezero]
      -- p > 1
      . rcases (le_or_gt k 12) with h3 | h3
        -- k ≤ 12, interval_cases p, k
        . interval_cases p
          all_goals
            interval_cases k
            all_goals
              try {norm_num}
              try {norm_num at h_pp}
        -- k > 12, p ^ k > 12 → p ^ k ≠ 12
        . exact Nat.ne_of_lt (Nat.lt_trans h3 (Nat.lt_pow_self h2))
    -- p > 12 → k > 0 → p ^ k ≠ 12
    . exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.gt_of_not_le h1) (Nat.le_self_pow h_knezero p))
  have r4 : ∀ p k, ¬ (p.Prime ∧ Odd p ∧ k > 0 ∧ 12 = 2 * p ^ k) := by
    simp only [not_and]
    rintro p k h_pp h_op h_kpos
    have h_knezero : ¬ k = 0 := Nat.not_eq_zero_of_lt h_kpos
    rcases (le_or_gt p 6) with h1 | h1
    -- p ≤ 6
    . rcases (le_or_gt p 1) with h2 | h2
      -- p = 0, 1, interval_cases p
      . interval_cases p
        all_goals simp [h_knezero]
      -- p > 1
      . rcases (le_or_gt k 6) with h3 | h3
        -- k ≤ 6, interval_cases p, k
        . interval_cases p
          all_goals
            interval_cases k
            all_goals
              try {norm_num}
              try {norm_num at h_pp}
        -- k > 6 → p ^ k > k → p ^ k > 6 → 2 * p ^ k > 12 → 2 * p ^ k ≠ 12
        . have : p ^ k > 6 := Nat.lt_trans h3 (Nat.lt_pow_self h2)
          have : 2 * p ^ k > 12 := Nat.mul_lt_mul_of_pos_left this Nat.zero_lt_two
          have : 2 * p ^ k ≠ 12 := Nat.ne_of_gt this
          exact Ne.symm this
    -- p > 6 → k > 0 → p ^ k ≠ 6 → 2 * p ^ k ≠ 12
    . have : p ^ k > 6 := Nat.lt_of_lt_of_le h1 (Nat.le_self_pow h_knezero p)
      have : 2 * p ^ k > 12 := Nat.mul_lt_mul_of_pos_left this Nat.zero_lt_two
      have : 2 * p ^ k ≠ 12 := Nat.ne_of_gt this
      exact Ne.symm this
  exact ⟨r1, r2, r3, r4⟩
