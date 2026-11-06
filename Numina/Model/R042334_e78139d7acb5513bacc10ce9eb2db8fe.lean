import Mathlib

open Nat

theorem number_theory_314867 (x : ℤ) :
    ∑ i ∈ Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ = 1001 ↔ x = 584 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 584.
    intro h
    have h1 : x ≤ 584 := by
      by_contra h2
      push_neg at h2
      have h2' : x ≥ 585 := by omega
      have h3 : ∑ i in Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ ≥ 1002 := by
        have h4 : x ≥ 585 := h2'
        have h5 : (x : ℝ) ≥ (585 : ℝ) := by exact_mod_cast h4
        have h6 : ∑ i in Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ ≥ ∑ i in Finset.Icc 1 10, ⌊(585 : ℝ) / Nat.factorial i⌋ := by
          apply Finset.sum_le_sum
          intro i hi
          have h7 : (x : ℝ) ≥ (585 : ℝ) := h5
          have h8 : (x : ℝ) / (Nat.factorial i : ℝ) ≥ (585 : ℝ) / (Nat.factorial i : ℝ) := by
            have h9 : (Nat.factorial i : ℝ) > 0 := by
              have h9 : i ≥ 1 := by
                have h9 : i ∈ Finset.Icc 1 10 := by
                  exact hi
                simp at h9 ⊢
                all_goals omega
              have h10 : Nat.factorial i > 0 := by
                apply Nat.factorial_pos
              have h11 : (Nat.factorial i : ℝ) > (0 : ℝ) := by exact_mod_cast h10
              linarith
            apply (div_le_div_right h9).mpr
            linarith
          have h11 : ⌊(x : ℝ) / (Nat.factorial i : ℝ)⌋ ≥ ⌊(585 : ℝ) / (Nat.factorial i : ℝ)⌋ := by
            apply Int.floor_le_floor
            linarith
          exact h11
        have h11 : ∑ i in Finset.Icc 1 10, ⌊(585 : ℝ) / Nat.factorial i⌋ = 1002 := by
          norm_num [Finset.sum_Icc_succ_top, Int.floor_eq_iff, Nat.factorial]
        linarith
      linarith
    have h2 : x ≥ 584 := by
      by_contra h3
      push_neg at h3
      have h4 : x ≤ 583 := by omega
      have h3' : ∑ i in Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ ≤ 999 := by
        have h4' : x ≤ 583 := h4
        have h5 : (x : ℝ) ≤ (583 : ℝ) := by exact_mod_cast h4'
        have h6 : ∑ i in Finset.Icc 1 10, ⌊(x : ℝ) / Nat.factorial i⌋ ≤ ∑ i in Finset.Icc 1 10, ⌊(583 : ℝ) / Nat.factorial i⌋ := by
          apply Finset.sum_le_sum
          intro i hi
          have h7 : (x : ℝ) ≤ (583 : ℝ) := h5
          have h8 : (x : ℝ) / (Nat.factorial i : ℝ) ≤ (583 : ℝ) / (Nat.factorial i : ℝ) := by
            have h9 : (Nat.factorial i : ℝ) > 0 := by
              have h9 : i ≥ 1 := by
                have h9 : i ∈ Finset.Icc 1 10 := by
                  exact hi
                simp at h9 ⊢
                all_goals omega
              have h10 : Nat.factorial i > 0 := by
                apply Nat.factorial_pos
              have h11 : (Nat.factorial i : ℝ) > (0 : ℝ) := by exact_mod_cast h10
              linarith
            apply (div_le_div_right h9).mpr
            linarith
          have h11 : ⌊(x : ℝ) / (Nat.factorial i : ℝ)⌋ ≤ ⌊(583 : ℝ) / (Nat.factorial i : ℝ)⌋ := by
            apply Int.floor_le_floor
            linarith
          exact h11
        have h11 : ∑ i in Finset.Icc 1 10, ⌊(583 : ℝ) / Nat.factorial i⌋ = 999 := by
          norm_num [Finset.sum_Icc_succ_top, Int.floor_eq_iff, Nat.factorial]
        linarith
      linarith
    have h3 : x = 584 := by omega
    exact h3
  · -- Backward direction: if x = 584, then the equation holds.
    intro h
    rw [h]
    norm_num [Finset.sum_Icc_succ_top, Int.floor_eq_iff, Nat.factorial]