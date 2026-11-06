import Mathlib

theorem number_theory_100513 (x : ℤ) :
    ∑ i ∈ Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ = 1001 ↔ x = 584 := by
  constructor
  · -- Assume the sum equals 1001, prove x = 584
    intro h
    have h1 : x ≤ 584 := by
      by_contra h2
      push_neg at h2
      have h3 : x ≥ 585 := by omega
      have h4 : ∑ i in Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ ≥ ∑ i in Finset.Icc 1 10, ⌊(585 : ℝ) / Nat.factorial i⌋ := by
        apply Finset.sum_le_sum
        intro i hi
        have h585 : (x : ℝ) ≥ (585 : ℝ) := by exact_mod_cast show (x : ℤ) ≥ (585 : ℤ) by linarith
        have h7 : (x : ℝ) / (Nat.factorial i : ℝ) ≥ (585 : ℝ) / (Nat.factorial i : ℝ) := by
          have h10 : (Nat.factorial i : ℝ) > 0 := by
            positivity
          apply (div_le_div_right h10).mpr
          linarith
        have h8 : ⌊(x : ℝ) / (Nat.factorial i : ℝ)⌋ ≥ ⌊(585 : ℝ) / (Nat.factorial i : ℝ)⌋ := by
          exact Int.floor_le_floor h7
        simpa using h8
      have h5 : ∑ i in Finset.Icc 1 10, ⌊(585 : ℝ) / Nat.factorial i⌋ = 1002 := by
        norm_num [Finset.sum_Icc_succ_top, Nat.factorial, Int.floor_eq_iff]
      have h6 : ∑ i in Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ ≥ 1002 := by
        linarith [h4, h5]
      linarith
    have h2 : x ≥ 584 := by
      by_contra h3
      push_neg at h3
      have h4 : x ≤ 583 := by omega
      have h30 : ∑ i in Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ ≤ ∑ i in Finset.Icc 1 10, ⌊(583 : ℝ) / Nat.factorial i⌋ := by
        apply Finset.sum_le_sum
        intro i hi
        have h7 : (x : ℝ) ≤ (583 : ℝ) := by exact_mod_cast show (x : ℤ) ≤ (583 : ℤ) by linarith
        have h71 : (x : ℝ) / (Nat.factorial i : ℝ) ≤ (583 : ℝ) / (Nat.factorial i : ℝ) := by
          have h10 : (Nat.factorial i : ℝ) > 0 := by
            positivity
          apply (div_le_div_right h10).mpr
          linarith
        have h8 : ⌊(x : ℝ) / (Nat.factorial i : ℝ)⌋ ≤ ⌊(583 : ℝ) / (Nat.factorial i : ℝ)⌋ := by
          exact Int.floor_le_floor h71
        simpa using h8
      have h31 : ∑ i in Finset.Icc 1 10, ⌊(583 : ℝ) / Nat.factorial i⌋ = 999 := by
        norm_num [Finset.sum_Icc_succ_top, Nat.factorial, Int.floor_eq_iff]
      have h32 : ∑ i in Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ ≤ 999 := by
        linarith [h30, h31]
      linarith
    linarith
  · -- Assume x = 584, prove the sum equals 1001
    intro h
    rw [show x = (584 : ℤ) by linarith]
    norm_num [Finset.sum_Icc_succ_top, Nat.factorial, Int.floor_eq_iff]