import Mathlib

theorem number_theory_191030 (x : ℕ) (hx : x > 0) :
    ∑ i ∈ Finset.Icc 1 10, ⌊(x / (Nat.factorial i) : ℝ)⌋ = 3468 ↔ x = 2020 := by
  constructor
  · -- Assume the sum equals 3468, prove x = 2020
    intro h
    have h1 : x ≤ 2020 := by
      by_contra h2
      push_neg at h2
      have h2' : ∑ i ∈ Finset.Icc 1 10, ⌊(x / (Nat.factorial i) : ℝ)⌋ > 3468 := by
        have h3 : x ≥ 2021 := by linarith
        have h4 : ∑ i ∈ Finset.Icc 1 10, ⌊(x / (Nat.factorial i) : ℝ)⌋ ≥ ∑ i ∈ Finset.Icc 1 10, ⌊(2021 / (Nat.factorial i) : ℝ)⌋ := by
          apply Finset.sum_le_sum
          intro i hi
          rcases Finset.mem_Icc.mp hi with ⟨h1, h2⟩
          have h5 : (x : ℝ) ≥ (2021 : ℝ) := by
            exact_mod_cast (show (x : ℝ) ≥ (2021 : ℝ) by
              have : x ≥ 2021 := by linarith
              exact_mod_cast this
            )
          have h6 : (x : ℝ) / (Nat.factorial i : ℝ) ≥ (2021 : ℝ) / (Nat.factorial i : ℝ) := by
            have h5' : (x : ℝ) ≥ (2021 : ℝ) := h5
            have h8 : (Nat.factorial i : ℝ) > 0 := by
              positivity
            apply (div_le_div_right (by positivity)).mpr
            exact_mod_cast h5'
          have : ⌊((x : ℝ) / (Nat.factorial i : ℝ))⌋ ≥ ⌊((2021 : ℝ) / (Nat.factorial i : ℝ))⌋ := by
            apply Int.floor_le_floor
            linarith
          exact_mod_cast this
        have h5 : ∑ i ∈ Finset.Icc 1 10, ⌊(2021 / (Nat.factorial i) : ℝ)⌋ = 3469 := by
          norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
          all_goals norm_num [Int.floor_eq_iff]
        linarith [h4, h5]
      linarith [h, h2']
    have h2 : x ≥ 2020 := by
      by_contra h3
      push_neg at h3
      have h3' : ∑ i ∈ Finset.Icc 1 10, ⌊(x / (Nat.factorial i) : ℝ)⌋ < 3468 := by
        have h4 : x ≤ 2019 := by
          omega
        have h5 : ∑ i ∈ Finset.Icc 1 10, ⌊(x / (Nat.factorial i) : ℝ)⌋ ≤ ∑ i ∈ Finset.Icc 1 10, ⌊(2019 / (Nat.factorial i) : ℝ)⌋ := by
          apply Finset.sum_le_sum
          intro i hi
          rcases Finset.mem_Icc.mp hi with ⟨h1, h2⟩
          have h5 : (x : ℝ) ≤ (2019 : ℝ) := by
            exact_mod_cast (show (x : ℝ) ≤ (2019 : ℝ) by
              have : x ≤ 2019 := by linarith
              exact_mod_cast this
            )
          have h6 : (x : ℝ) / (Nat.factorial i : ℝ) ≤ (2019 : ℝ) / (Nat.factorial i : ℝ) := by
            have h5' : (x : ℝ) ≤ (2019 : ℝ) := h5
            have h8 : (Nat.factorial i : ℝ) > 0 := by positivity
            apply (div_le_div_right (by positivity)).mpr
            exact_mod_cast h5'
          have : ⌊((x : ℝ) / (Nat.factorial i : ℝ))⌋ ≤ ⌊((2019 : ℝ) / (Nat.factorial i : ℝ))⌋ := by
            apply Int.floor_le_floor
            linarith
          exact_mod_cast this
        have h6 : ∑ i ∈ Finset.Icc 1 10, ⌊(2019 / (Nat.factorial i) : ℝ)⌋ = 3466 := by
          norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
          all_goals norm_num [Int.floor_eq_iff]
        linarith [h5, h6]
      linarith [h, h3']
    omega
  · -- Assume x = 2020, prove the sum equals 3468
    intro h
    rw [h]
    norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
    all_goals norm_num [Int.floor_eq_iff]
    <;> try { native_decide }