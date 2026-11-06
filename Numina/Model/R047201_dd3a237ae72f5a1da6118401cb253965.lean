import Mathlib

theorem number_theory_249502 :
    { (x, y) : ℕ × ℕ | x ≠ 0 ∧ y ≠ 0 ∧ x.lcm y = 4320 ∧ (12 ∣ x ∧ 20 ∣ x ∧ 45 ∣ x) ∧ (12 ∣ y ∧ 20 ∣ y ∧ 45 ∣ y) } =
    { (180, 4320), (360, 4320), (540, 4320), (720, 4320), (1080, 4320), (1440, 4320), (2160, 4320), (4320, 4320),(1440, 2160), (540, 1440), (1080, 1440),(4320, 180), (4320, 360), (4320, 540), (4320, 720), (4320, 1080), (4320, 1440), (4320, 2160), (2160, 1440), (1440, 540), (1440, 1080) } := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Forward implication: if (x, y) satisfies the conditions, then (x, y) ∈ RHS.
    rintro ⟨hx, hy, h1, ⟨hx12, hx20, hx45⟩, ⟨hy12, hy20, hy45⟩⟩
    have h2 : x % 180 = 0 := by
      omega
    have h3 : y % 180 = 0 := by
      omega
    have h4 : ∃ k, x = 180 * k := ⟨x / 180, by omega⟩
    have h5 : ∃ l, y = 180 * l := ⟨y / 180, by omega⟩
    rcases h4 with ⟨k, h4⟩
    rcases h5 with ⟨l, h5⟩
    have h6 : (180 * k).lcm (180 * l) = 4320 := by
      rw [show 180 * k = x by omega, show 180 * l = y by omega] 
      exact h1
    have h7 : k ≠ 0 := by 
      by_contra h 
      rw [h] at h4 
      omega 
    have h8 : l ≠ 0 := by 
      by_contra h 
      rw [h] at h5 
      omega
    have h8 : (180 * k).lcm (180 * l) = 180 * (k.lcm l) := by
      rw [Nat.lcm_mul_left]
      all_goals norm_num
    rw [h8] at h6 
    have h9 : k.lcm l = 24 := by 
      omega 
    have h10 : k ≤ 24 := by
      have h11 : k ∣ k.lcm l := by 
        exact Nat.dvd_lcm_left k l
      have h13 : k.lcm l = 24 := h9 
      have h13 : k ∣ 24 := by 
        rw [h13] at h11 
        exact h11 
      have h14 : k ≤ 24 := by 
        exact Nat.le_of_dvd (by linarith) h13 
      omega 
    have h11 : l ≤ 24 := by 
      have h12 : l ∣ k.lcm l := by 
        exact Nat.dvd_lcm_right k l 
      have h13 : k.lcm l = 24 := h9 
      have h14 : l ∣ 24 := by 
        rw [h13] at h12 
        exact h12 
      have h15 : l ≤ 24 := by 
        exact Nat.le_of_dvd (by linarith) h14 
      omega 
    interval_cases k <;> interval_cases l 
      <;> norm_num [h4, h5] at *
      <;> omega 
  · -- Backward implication: if (x, y) ∈ RHS, then it satisfies the conditions.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | 
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | 
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num [Nat.lcm]
      constructor
      · norm_num
      · norm_num