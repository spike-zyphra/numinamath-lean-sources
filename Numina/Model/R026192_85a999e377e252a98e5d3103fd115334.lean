import Mathlib

theorem number_theory_275561 (n : ℤ) :
    3 ∣ (n * (n + 1)) / 2 ∨ (n * (n + 1)) / 2 ≡ 1 [ZMOD 3] := by
  have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h1 with (h | h | h)
  · -- Assume n % 3 = 0
    have h2 : (n * (n + 1)) % 6 = 0 := by
      have h3 : n % 3 = 0 := h
      have h4 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h4 with (h4 | h4)
      · -- Assume n % 2 = 0
        have h5 : n % 6 = 0 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h5]
      · -- Assume n % 2 = 1
        have h5 : n % 6 = 3 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h5]
    have h2' : 3 ∣ (n * (n + 1)) / 2 := by
      have h3 : (n * (n + 1)) % 6 = 0 := h2
      have h4 : 6 ∣ n * (n + 1) := by
        omega
      obtain ⟨k, hk⟩ := show ∃k : ℤ, n * (n + 1) = 6 * k by
        refine ⟨(n * (n + 1)) / 6, by omega⟩
      have hk2 : (n * (n + 1)) / 2 = 3 * k := by
        omega
      rw [hk2] 
      all_goals omega
    left
    exact h2'
  · -- Assume n % 3 = 1
    have h2 : (n * (n + 1)) % 6 = 2 := by
      have h3 : n % 3 = 1 := h
      have h4 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h4 with (h4 | h4)
      · -- Assume n % 2 = 0
        have h5 : n % 6 = 4 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h5]
      · -- Assume n % 2 = 1
        have h5 : n % 6 = 1 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h5]
    have h2' : (n * (n + 1)) / 2 % 3 = 1 := by
      omega
    have h3 : (n * (n + 1)) / 2 ≡ 1 [ZMOD 3] := by
      simp [Int.ModEq] at *
      omega
    right
    exact h3
  · -- Assume n % 3 = 2
    have h2 : (n * (n + 1)) % 6 = 0 := by
      have h3 : n % 3 = 2 := h
      have h4 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h4 with (h4 | h4)
      · -- Assume n % 2 = 0
        have h5 : n % 6 = 2 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h5]
      · -- Assume n % 2 = 1
        have h5 : n % 6 = 5 := by
          omega
        simp [Int.add_emod, Int.mul_emod, h5]
    have h2' : 3 ∣ (n * (n + 1)) / 2 := by
      have h3 : (n * (n + 1)) % 6 = 0 := h2
      have h4 : 6 ∣ n * (n + 1) := by
        omega
      obtain ⟨k, hk⟩ := show ∃k : ℤ, n * (n + 1) = 6 * k by
        refine ⟨(n * (n + 1)) / 6, by omega⟩
      have hk2 : (n * (n + 1)) / 2 = 3 * k := by
        omega
      rw [hk2] 
      all_goals omega
    left
    exact h2'