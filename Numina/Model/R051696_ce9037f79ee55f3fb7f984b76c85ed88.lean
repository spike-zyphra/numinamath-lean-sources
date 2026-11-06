import Mathlib

theorem algebra_323419 : ∑ᶠ k ∈ {k : ℝ | ∃ x, x^2 - 3 * x + 2 = 0 ∧ x^2 - 5 * x + k = 0}, k = 10 := by
  have h1 : {k : ℝ | ∃ x, x^2 - 3 * x + 2 = 0 ∧ x^2 - 5 * x + k = 0} = {4, 6} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- If k is in the set, then k = 4 or 6
      intro hk
      rcases hk with ⟨x, hx1, hx2⟩
      have h1 : x^2 - 3 * x + 2 = 0 := hx1
      have h2 : x^2 - 5 * x + k = 0 := hx2
      have h3 : (x - 1) * (x - 2) = 0 := by linarith
      cases' (mul_eq_zero.mp h3) with h4 h5
      · -- Case x = 1
        have hx1_eq : x = 1 := by linarith
        rw [hx1_eq] at h2
        have hk_eq_4 : k = 4 := by linarith
        left
        linarith
      · -- Case x = 2
        have hx2_eq : x = 2 := by linarith
        rw [hx2_eq] at h2
        have hk_eq_6 : k = 6 := by linarith
        right
        linarith
    · -- If k = 4 or 6, then k is in the set
      rintro (hk4 | hk6)
      · -- k = 4
        rw [hk4]
        use 1
        constructor
        · norm_num
        · norm_num
      · -- k = 6
        rw [hk6]
        use 2
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [finsum_mem_pair]
  all_goals norm_num