import Mathlib

theorem algebra_98049 (s : Set ℤ) (hs : s = {k : ℤ | ∃ x : ℝ, x^2 - 3 * x + 2 = 0 ∧ x^2 - 5 * x + k = 0}) :
    ∑ᶠ i ∈ s, i = 10 := by

  have h1 : s = {4, 6} := by
    ext k
    simp only [hs, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume k ∈ s, so there exists x such that both equations hold
      rintro ⟨x, hx1, hx2⟩
      have h2 : x^2 - 3 * x + 2 = 0 := hx1
      have h3 : (x - 1) * (x - 2) = 0 := by linarith
      cases' (mul_eq_zero.1 h3) with h4 h5
      · -- Case x - 1 = 0, so x = 1
        have hx : x = 1 := by linarith
        rw [hx] at hx2
        have hk : (k : ℝ) = 4 := by
          nlinarith
        have hk' : k = 4 := by
          exact_mod_cast hk
        simp [hk']
      · -- Case x - 2 = 0, so x = 2
        have hx : x = 2 := by linarith
        rw [hx] at hx2
        have hk : (k : ℝ) = 6 := by
          nlinarith
        have hk' : k = 6 := by
          exact_mod_cast hk
        simp [hk']
    · -- Assume k = 4 or k = 6, need to show k ∈ s
      rintro (h | h)
      · -- Case k = 4
        rw [show k = 4 by linarith] 
        use 1
        norm_num
      · -- Case k = 6
        rw [show k = 6 by linarith]
        use 2
        norm_num

  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num