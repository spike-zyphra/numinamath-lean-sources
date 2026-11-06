import Mathlib

theorem algebra_12291 {a b : ℕ} (ha : IsLeast {n | 0 < n ∧ n ∈ Finset.Icc 10 99 ∧ 3 ∣ n} a)
    (hb : IsLeast {n | 0 < n ∧ n ∈ Finset.Icc 100 999 ∧ 4 ∣ n} b) :
    a + b = 112 := by

  have ha1 : a ∈ {n | 0 < n ∧ n ∈ Finset.Icc 10 99 ∧ 3 ∣ n} := by
    exact ha.1
  rcases ha1 with ⟨ha_pos, ha_in_range, ha_div3⟩
  rw [Finset.mem_Icc] at ha_in_range
  have h3 : a = 12 := by
    have h4 : ∀ n, (0 < n ∧ n ∈ Finset.Icc 10 99 ∧ 3 ∣ n) → a ≤ n := by
      apply ha.2
    have h5 : a ≤ 12 := by
      specialize h4 12 (by
        constructor
        · norm_num
        constructor
        · norm_num [Finset.mem_Icc]
        · norm_num
      )
      linarith
    have h6 : a ≥ 12 := by
      by_contra h
      push_neg at h
      have h7 : a < 12 := by linarith
      have h8 : a ≥ 10 := by omega
      interval_cases a <;> norm_num at ha_div3 <;> omega
    linarith
  have hb1 : b ∈ {n | 0 < n ∧ n ∈ Finset.Icc 100 999 ∧ 4 ∣ n} := by
    exact hb.1
  rcases hb1 with ⟨hb_pos, hb_in_range, hb_div4⟩
  rw [Finset.mem_Icc] at hb_in_range
  have h99 : b = 100 := by
    have h7 : ∀ n, (0 < n ∧ n ∈ Finset.Icc 100 999 ∧ 4 ∣ n) → b ≤ n := by
      apply hb.2
    have h8 : b ≤ 100 := by
      specialize h7 100 (by
        constructor
        · norm_num
        constructor
        · norm_num [Finset.mem_Icc]
        · norm_num
      )
      linarith
    have h11 : b ≥ 100 := by
      omega
    linarith
  omega