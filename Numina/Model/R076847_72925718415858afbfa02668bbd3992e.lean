import Mathlib

theorem algebra_301077 (x : ℝ) :
    ⌊2 * x⌋ + ⌊3 * x⌋ = 8 * x - 7 / 2 ↔ x = 13 / 16 ∨ x = 17 / 16 := by
  constructor
  · -- Forward direction: equation implies solutions
    intro h
    have h1 : (⌊2 * x⌋ : ℝ) + (⌊3 * x⌋ : ℝ) = 8 * x - 7 / 2 := by
      exact_mod_cast h
    have h2 : ∃ k : ℤ, (⌊2 * x⌋ + ⌊3 * x⌋ : ℝ) = (k : ℝ) := by
      refine' ⟨⌊2 * x⌋ + ⌊3 * x⌋, by simp⟩
    rcases h2 with ⟨k, hk2⟩
    have hk_eq : k = 8 * x - 7 / 2 := by
      have h3 : ((⌊2 * x⌋ + ⌊3 * x⌋ : ℝ) ) = (k : ℝ) := by
        exact_mod_cast hk2
      linarith [h1, h3]
    have hx : x = (2 * k + 7) / 16 := by
      have h4 : (k : ℝ) = 8 * x - 7 / 2 := by
        exact_mod_cast hk_eq
      linarith
    have h3 : k ≤ 5 := by
      have hk1 : (⌊2 * x⌋ : ℝ) ≤ 2 * x := by
        exact Int.floor_le (2 * x)
      have hk2 : (⌊3 * x⌋ : ℝ) ≤ 3 * x := by
        exact Int.floor_le (3 * x)
      have h4 : (⌊2 * x⌋ + ⌊3 * x⌋ : ℝ) ≤ 5 * x := by
        linarith [hk1, hk2]
      have h5 : (k : ℝ) ≤ 5 * x := by
        linarith [h1, h4]
      rw [hx] at h5
      have h6 : (k : ℝ) ≤ 5 * ((2 * k + 7) / 16) := by linarith
      have h7 : (k : ℝ) ≤ 35 / 6 := by
        nlinarith
      by_contra h8
      push_neg at h8
      have h9 : k ≥ 6 := by omega
      have h10 : (k : ℝ) ≥ (6 : ℝ) := by exact_mod_cast h9
      linarith
    have h4 : k > 0 := by
      have hk1 : 2 * x < (⌊2 * x⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one (2 * x)
      have hk2 : 3 * x < (⌊3 * x⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one (3 * x)
      have h5 : 5 * x < (⌊2 * x⌋ + ⌊3 * x⌋ + 2 : ℝ) := by
        linarith [hk1, hk2]
      have h6 : 5 * x < (k + 2 : ℝ) := by
        linarith [h1, h5]
      rw [hx] at h6
      have h7 : 5 * ((2 * k + 7) / 16) < (k + 2 : ℝ) := by linarith
      have h8 : (k : ℝ) > 1 / 2 := by
        nlinarith
      by_contra h9
      push_neg at h9
      have h10 : k ≤ 0 := by omega
      have h11 : (k : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h10
      linarith
    have hk1 : k ≤ 5 := by omega
    have hk2 : k ≥ 1 := by omega
    have h5 : k = 3 ∨ k = 5 := by
      interval_cases k <;> norm_num [hx] at *
      <;> simp [hx] at h1
      <;> norm_num at h1
      <;> tauto
    rcases h5 with (hk | hk)
    · -- k = 3
      have hx1 : x = 13 / 16 := by
        rw [hx]
        norm_num [hk]
      left
      exact hx1
    · -- k = 5
      have hx2 : x = 17 / 16 := by
        rw [hx]
        norm_num [hk]
      right
      exact hx2
  · -- Backward direction: solutions satisfy the equation
    rintro (h | h)
    · -- x = 13/16
      rw [h]
      norm_num
      <;> try { norm_num }
    · -- x = 17/16
      rw [h]
      norm_num
      <;> try { norm_num }