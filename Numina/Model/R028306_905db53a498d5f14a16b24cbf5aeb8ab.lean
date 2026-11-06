import Mathlib

open Real

theorem inequalities_253693 :
    Set.ncard {n : ℕ | 0 < n ∧ 2000 < sqrt (n * (n - 1)) ∧ sqrt (n * (n - 1)) < 2005} = 5 := by

  have h1 : {n : ℕ | 0 < n ∧ 2000 < sqrt (n * (n - 1)) ∧ sqrt (n * (n - 1)) < 2005} = {2001, 2002, 2003, 2004, 2005} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume $0 < n ∧ 2000 < \sqrt(n * (n - 1)) ∧ \sqrt(n * (n - 1)) < 2005$, show $n = 2001 ∨ n = 2002 ∨ n = 2003 ∨ n = 2004 ∨ n = 2005$.
      intro h
      rcases h with ⟨hn_pos, h2, h3⟩
      have h4 : n > 0 := by linarith
      have h5 : n ≥ 1 := by omega

      have h8 : (2000 : ℝ) < sqrt (n * (n - 1 : ℝ)) := by
        have h8 : (2000 : ℝ) < sqrt (n * (n - 1 : ℝ)) := by
          simpa using h2
        linarith
      have h9 : sqrt (n * (n - 1 : ℝ)) < (2005 : ℝ) := by
        have h9 : sqrt (n * (n - 1 : ℝ)) < (2005 : ℝ) := by
          simpa using h3
        linarith

      have h10 : (2000 : ℝ) ^ 2 < (n * (n - 1 : ℝ)) := by
        have h11 : (2000 : ℝ) < sqrt (n * (n - 1 : ℝ)) := h8
        have h12 : (2000 : ℝ) ^ 2 < (sqrt (n * (n - 1 : ℝ)) : ℝ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (n * (n - 1 : ℝ)), show (2000 : ℝ) ≥ 0 by norm_num]
        have h13 : (sqrt (n * (n - 1 : ℝ)) : ℝ) ^ 2 = (n * (n - 1 : ℝ)) := by
          rw [Real.sq_sqrt]
          have h5' : (n * (n - 1 : ℝ)) ≥ 0 := by
            have h8 : (n : ℝ) ≥ 1 := by exact_mod_cast show n ≥ 1 by omega
            have h9 : (n - 1 : ℝ) ≥ 0 := by
              nlinarith
            nlinarith [show (n : ℝ) ≥ 0 by linarith]
          linarith
        linarith

      have h10' : (n * (n - 1 : ℝ)) < (2005 : ℝ) ^ 2 := by
        have h11 : sqrt (n * (n - 1 : ℝ)) < (2005 : ℝ) := h9
        have h12 : (sqrt (n * (n - 1 : ℝ)) : ℝ) ^ 2 < (2005 : ℝ) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (n * (n - 1 : ℝ)), show (2005 : ℝ) ≥ 0 by norm_num]
        have h13 : (sqrt (n * (n - 1 : ℝ)) : ℝ) ^ 2 = (n * (n - 1 : ℝ)) := by
          rw [Real.sq_sqrt]
          have h5' : (n * (n - 1 : ℝ)) ≥ 0 := by
            have h8 : (n : ℝ) ≥ 1 := by exact_mod_cast show n ≥ 1 by omega
            have h9 : (n - 1 : ℝ) ≥ 0 := by
              nlinarith
            nlinarith [show (n : ℝ) ≥ 0 by linarith]
          linarith
        linarith

      have h100 : (4000000 : ℝ) < (n * (n - 1 : ℝ)) := by
        norm_num at h10 ⊢
        linarith

      have h101 : (n * (n - 1 : ℝ)) < (4020025 : ℝ) := by
        norm_num at h10' ⊢
        linarith

      have h14 : (4000000 : ℤ) < n * (n - 1 : ℤ) := by
        have h16 : (n * (n - 1 : ℝ)) > (4000000 : ℝ) := by linarith
        have h17 : (n * (n - 1 : ℝ)) = (n * (n - 1 : ℤ) : ℝ) := by
          simp
        rw [h17] at h16
        exact_mod_cast h16

      have h15 : (n * (n - 1 : ℤ) : ℤ) < (4020025 : ℤ) := by
        have h18 : (n * (n - 1 : ℝ)) < (4020025 : ℝ) := by linarith
        have h19 : (n * (n - 1 : ℝ)) = (n * (n - 1 : ℤ) : ℝ) := by
          simp
        rw [h19] at h18
        exact_mod_cast h18

      have h1200 : n ≥ 2001 := by
        by_contra h
        push_neg at h
        have h20 : n ≤ 2000 := by omega
        have h22 : n ≤ 2000 := by omega
        have h23 : (n : ℤ) ≤ (2000 : ℤ) := by exact_mod_cast h22
        have h24 : (n - 1 : ℤ) ≤ (1999 : ℤ) := by
          nlinarith
        have h25 : (n : ℤ) * (n - 1 : ℤ) ≤ (2000 : ℤ) * (1999 : ℤ) := by
          nlinarith
        nlinarith

      have h1230 : n ≤ 2005 := by
        by_contra h
        push_neg at h
        have h30 : n ≥ 2006 := by omega
        have h31 : (n : ℤ) ≥ (2006 : ℤ) := by exact_mod_cast h30
        have h32 : (n - 1 : ℤ) ≥ (2005 : ℤ) := by
          nlinarith
        have h33 : (n : ℤ) * (n - 1 : ℤ) ≥ (2006 : ℤ) * (2005 : ℤ) := by
          nlinarith
        nlinarith

      interval_cases n <;> norm_num at h14 h15 ⊢
    · -- Assume $n = 2001 ∨ n = 2002 ∨ n = 2003 ∨ n = 2004 ∨ n = 2005$, show $0 < n ∧ 2000 < \sqrt(n * (n - 1)) ∧ \sqrt(n * (n - 1)) < 2005$.
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- When n = 2001
        constructor
        · norm_num
        constructor
        · -- Show 2000 < sqrt (2001 * 2000)
          rw [Real.lt_sqrt] <;> norm_num
        · -- Show sqrt (2001 * 2000) < 2005
          rw [Real.sqrt_lt] <;> norm_num
      · -- When n = 2002
        constructor
        · norm_num
        constructor
        · -- Show 2000 < sqrt (2002 * 2001)
          rw [Real.lt_sqrt] <;> norm_num
        · -- Show sqrt (2002 * 2001) < 2005
          rw [Real.sqrt_lt] <;> norm_num
      · -- When n = 2003
        constructor
        · norm_num
        constructor
        · -- Show 2000 < sqrt (2003 * 2002)
          rw [Real.lt_sqrt] <;> norm_num
        · -- Show sqrt (2003 * 2002) < 2005
          rw [Real.sqrt_lt] <;> norm_num
      · -- When n = 2004
        constructor
        · norm_num
        constructor
        · -- Show 2000 < sqrt (2004 * 2003)
          rw [Real.lt_sqrt] <;> norm_num
        · -- Show sqrt (2004 * 2003) < 2005
          rw [Real.sqrt_lt] <;> norm_num
      · -- When n = 2005
        constructor
        · norm_num
        constructor
        · -- Show 2000 < sqrt (2005 * 2004)
          rw [Real.lt_sqrt] <;> norm_num
        · -- Show sqrt (2005 * 2004) < 2005
          rw [Real.sqrt_lt] <;> norm_num

  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]