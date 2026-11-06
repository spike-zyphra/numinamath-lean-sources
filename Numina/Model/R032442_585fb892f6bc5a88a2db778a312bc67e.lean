import Mathlib

theorem number_theory_81935 : IsGreatest {n : ℕ | n > 0 ∧ ⌊Real.sqrt n⌋ - 2 ∣ n - 4 ∧ ⌊Real.sqrt n⌋ + 2 ∣ n + 4 ∧ n < 1000} 956 := by
  constructor
  · -- Show 956 is in the set
    constructor
    · norm_num
    constructor
    · -- Check that ⌊√956⌋ - 2 divides 956 - 4
      have h1 : ⌊Real.sqrt (956 : ℕ)⌋ = 30 := by
        have h2 : Real.sqrt (956 : ℕ) = Real.sqrt (956 : ℝ) := by simp
        rw [h2]
        have h8 : ⌊Real.sqrt (956 : ℝ)⌋ = 30 := by
          have h9 : Real.sqrt (956 : ℝ) < (31 : ℝ) := by
            nlinarith [Real.sqrt_nonneg (956 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (956 : ℝ) by norm_num), sq_nonneg (Real.sqrt (956 : ℝ) - 31)]
          have h10 : 30 ≤ Real.sqrt (956 : ℝ) := by
            nlinarith [Real.sqrt_nonneg (956 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (956 : ℝ) by norm_num), sq_nonneg (Real.sqrt (956 : ℝ) - 30)]
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> try linarith
        exact h8
      rw [h1]
      all_goals norm_num
    constructor
    · -- Check that ⌊√956⌋ + 2 divides 956 + 4
      have h1 : ⌊Real.sqrt (956 : ℕ)⌋ = 30 := by
        have h2 : Real.sqrt (956 : ℕ) = Real.sqrt (956 : ℝ) := by simp
        rw [h2]
        have h8 : ⌊Real.sqrt (956 : ℝ)⌋ = 30 := by
          have h9 : Real.sqrt (956 : ℝ) < (31 : ℝ) := by
            nlinarith [Real.sqrt_nonneg (956 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (956 : ℝ) by norm_num), sq_nonneg (Real.sqrt (956 : ℝ) - 31)]
          have h10 : 30 ≤ Real.sqrt (956 : ℝ) := by
            nlinarith [Real.sqrt_nonneg (956 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (956 : ℝ) by norm_num), sq_nonneg (Real.sqrt (956 : ℝ) - 30)]
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> try linarith
        exact h8
      rw [h1]
      all_goals norm_num
    · -- Show 956 < 1000
      norm_num
  · -- Show there is no greater element in the set
    intro n hn
    rcases hn with ⟨hn_pos, h1, h2, hn_lt⟩
    by_contra h
    push_neg at h
    have h3 : n > 956 := by linarith
    have h4 : n < 1000 := by linarith
    have h5 : ⌊Real.sqrt (n : ℕ)⌋ = 30 ∨ ⌊Real.sqrt (n : ℕ)⌋ = 31 := by
      have h5 : (n : ℝ) < (1000 : ℝ) := by exact_mod_cast (show n < 1000 by linarith)
      have h6 : Real.sqrt (n : ℝ) < Real.sqrt (1000 : ℝ) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
      have h7 : Real.sqrt (1000 : ℝ) < 32 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1000 by norm_num : (0 : ℝ) ≤ 1000), Real.sqrt_nonneg 1000]
      have h8 : Real.sqrt (n : ℝ) < 32 := by linarith [h6, h7]
      have h9 : ⌊Real.sqrt (n : ℕ)⌋ ≤ 31 := by
        have h10 : Real.sqrt (n : ℝ) < 32 := by linarith [h6, h7]
        have h11 : ⌊Real.sqrt (n : ℝ)⌋ ≤ 31 := by
          by_contra h
          push_neg at h
          have h12 : ⌊Real.sqrt (n : ℝ)⌋ ≥ 32 := by omega
          have h13 : Real.sqrt (n : ℝ) ≥ (⌊Real.sqrt (n : ℝ)⌋ : ℝ) := by
            exact_mod_cast (show ⌊Real.sqrt (n : ℝ)⌋ ≤ Real.sqrt (n : ℝ) by exact_mod_cast (Int.floor_le (Real.sqrt (n : ℝ)))) 
          have h14 : Real.sqrt (n : ℝ) ≥ (32 : ℝ) := by
            have h15 : (⌊Real.sqrt (n : ℝ)⌋ : ℝ) ≥ (32 : ℝ) := by exact_mod_cast h12
            nlinarith [h13, h15]
          linarith
        exact_mod_cast h11
      have h10 : ⌊Real.sqrt (n : ℕ)⌋ ≥ 30 := by
        by_contra h
        push_neg at h
        have h11 : ⌊Real.sqrt (n : ℕ)⌋ ≤ 29 := by omega
        have h12 : Real.sqrt (n : ℝ) < (30 : ℝ) := by
          have h13 : ⌊Real.sqrt (n : ℝ)⌋ ≤ 29 := by omega
          have h14 : Real.sqrt (n : ℝ) < (⌊Real.sqrt (n : ℝ)⌋ + 1 : ℝ) := by
            exact_mod_cast (show Real.sqrt (n : ℝ) < ⌊Real.sqrt (n : ℝ)⌋ + 1 by exact_mod_cast (Int.lt_floor_add_one (Real.sqrt (n : ℝ))))
          have h15 : (⌊Real.sqrt (n : ℝ)⌋ + 1 : ℝ) ≤ (30 : ℝ) := by
            have h16 : (⌊Real.sqrt (n : ℝ)⌋ : ℝ) ≤ (29 : ℝ) := by exact_mod_cast h13
            have h17 : (⌊Real.sqrt (n : ℝ)⌋ + 1 : ℝ) ≤ (29 + 1 : ℝ) := by
              linarith [h16]
            norm_num at h17 ⊢
            all_goals try linarith
          nlinarith [h14, h15]
        have h13 : (n : ℝ) < (900 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith), h12]
        have h14 : n < 900 := by exact_mod_cast h13
        omega
      omega
    rcases h5 with (h_eq30 | h_eq31)
    · -- Assume ⌊√n⌋ = 30
      rw [h_eq30] at h1 h2
      interval_cases n <;> norm_num at h1 h2 h_eq30 hn_pos hn_lt
      <;> try { tauto }
      <;> norm_num
      <;> try { tauto }
      <;> norm_num
    · -- Assume ⌊√n⌋ = 31
      rw [h_eq31] at h1 h2
      interval_cases n <;> norm_num at h1 h2 h_eq31 hn_pos hn_lt
      <;> try { tauto }
      <;> norm_num
      <;> try { tauto }
      <;> norm_num