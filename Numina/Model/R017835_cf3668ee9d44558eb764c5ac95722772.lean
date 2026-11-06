import Mathlib

theorem number_theory_220379 (x : ℕ) (hx : x > 0) :
    ∑ i ∈ Finset.Icc 1 10, ⌊(x / Nat.factorial i : ℝ)⌋ = 1001 ↔ x = 584 := by
  constructor
  · -- Assume the sum equals 1001, prove x = 584
    intro h
    have h1 : x ≤ 584 := by
      by_contra h2
      push_neg at h2
      have h2 : x ≥ 585 := by omega
      have h2 : ∑ i ∈ Finset.Icc 1 10, ⌊(x / Nat.factorial i : ℝ)⌋ ≥ ∑ i ∈ Finset.Icc 1 10, ⌊(585 / Nat.factorial i : ℝ)⌋ := by
        apply Finset.sum_le_sum
        intro i hi
        have h3 : (x / Nat.factorial i : ℝ) ≥ (585 / Nat.factorial i : ℝ) := by
          have hf : (Nat.factorial i : ℝ) > 0 := by positivity
          have hx_i : (x : ℝ) ≥ (585 : ℝ) := by exact_mod_cast (show x ≥ 585 by omega)
          have h5 : (x / Nat.factorial i : ℝ) = (x : ℝ) / (Nat.factorial i : ℝ) := by rfl
          have h6 : (585 / Nat.factorial i : ℝ) = (585 : ℝ) / (Nat.factorial i : ℝ) := by rfl
          rw [h5, h6]
          apply (div_le_div_right hf).mpr hx_i
        have h4 : ⌊(x / Nat.factorial i : ℝ)⌋ ≥ ⌊(585 / Nat.factorial i : ℝ)⌋ := by
          apply Int.floor_le_floor
          linarith
        linarith
      have h3 : ∑ i ∈ Finset.Icc 1 10, ⌊(585 / Nat.factorial i : ℝ)⌋ = 1002 := by
        norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
      have h4 : ∑ i ∈ Finset.Icc 1 10, ⌊(x / Nat.factorial i : ℝ)⌋ ≥ 1002 := by
        linarith
      omega
    have h2 : x ≤ 584 := h1
    have h3 : x ≥ 584 := by
      by_contra h2
      push_neg at h2
      have h4 : x ≤ 583 := by omega
      have h4 : ∑ i ∈ Finset.Icc 1 10, ⌊(x / Nat.factorial i : ℝ)⌋ < 1001 := by
        have h4 : x ≤ 583 := by omega
        have h4 : ∑ i ∈ Finset.Icc 1 10, ⌊(x / Nat.factorial i : ℝ)⌋ ≤ ∑ i ∈ Finset.Icc 1 10, ⌊(583 / Nat.factorial i : ℝ)⌋ := by
          apply Finset.sum_le_sum
          intro i hi
          have h3 : (x / Nat.factorial i : ℝ) ≤ (583 / Nat.factorial i : ℝ) := by
            have hf : (Nat.factorial i : ℝ) > 0 := by positivity
            have hx_i : (x : ℝ) ≤ (583 : ℝ) := by exact_mod_cast (show x ≤ 583 by omega)
            have h5 : (x / Nat.factorial i : ℝ) = (x : ℝ) / (Nat.factorial i : ℝ) := by rfl
            have h6 : (583 / Nat.factorial i : ℝ) = (583 : ℝ) / (Nat.factorial i : ℝ) := by rfl
            rw [h5, h6]
            apply (div_le_div_right hf).mpr hx_i
          have h4 : ⌊(x / Nat.factorial i : ℝ)⌋ ≤ ⌊(583 / Nat.factorial i : ℝ)⌋ := by
            apply Int.floor_le_floor
            linarith
          linarith
        have h5 : ∑ i ∈ Finset.Icc 1 10, ⌊(583 / Nat.factorial i : ℝ)⌋ = 999 := by
          norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
        have h6 : ∑ i ∈ Finset.Icc 1 10, ⌊(x / Nat.factorial i : ℝ)⌋ ≤ 999 := by
          linarith
        omega
      omega
    have hx : x = 584 := by
      linarith
    tauto
  · -- Assume x = 584, prove the sum equals 1001
    rintro h
    rw [h]
    norm_num [Finset.sum_Icc_succ_top, Nat.factorial]