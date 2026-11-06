import Mathlib

open Real Set


theorem calculus_11387 {a b : ℝ} (ha : a ∈ Ioo 0 (π / 2)) (hb : b ∈ Ioo 0 (π / 2))
    (h1 : 3 * sin a ^ 2 + 2 * sin b ^ 2 = 1) (h2 : 3 * sin (2 * a) - 2 * sin (2 * b) = 0) :
    a + 2 * b = π / 2 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with  ⟨hb1, hb2⟩

  have h3 : sin (2 * a) = 2 * sin a * cos a := by
    rw [sin_two_mul]

  have h4 : sin (2 * b) = 2 * sin b * cos b := by
    rw [sin_two_mul]

  rw [h3, h4] at h2

  have h5 : 3 * sin a * cos a = 2 * sin b * cos b := by
    nlinarith

  have h6 : cos (a + 2 * b) = cos a * cos (2 * b) - sin a * sin (2 * b) := by
    rw [cos_add]

  have h7 : sin (2 * b) = 3 * sin a * cos a := by
    nlinarith

  have h9 : cos (2 * b) = 3 * sin a ^ 2 := by
    have h11 : cos (2 * b) = 2 * cos b ^ 2 - 1 := by
      rw [cos_two_mul]
    have h10 : cos b ^ 2 = (1 + 3 * sin a ^ 2) / 2 := by
      have h13 : sin b ^ 2 = (1 - 3 * sin a ^ 2) / 2 := by
        nlinarith
      have h10 : cos b ^ 2 = 1 - sin b ^ 2 := by
        have h11 : cos b ^ 2 + sin b ^ 2 = 1 := by
          exact Real.cos_sq_add_sin_sq b
        linarith
      rw [h13] at h10
      nlinarith
    rw [h10] at h11
    nlinarith

  have h12 : cos (a + 2 * b) = 0 := by
    rw [h6]
    rw [h9, h7]
    ring_nf

  have h13 : a + 2 * b = Real.pi / 2 := by
    have h14 : a + 2 * b > 0 := by
      nlinarith [Real.pi_pos]
    have h15 : a + 2 * b < 3 * Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have h16 : ∃ k : ℤ, a + 2 * b = Real.pi / 2 + k * Real.pi := by
      rw [Real.cos_eq_zero_iff] at h12
      rcases h12 with ⟨k, hk⟩
      use k
      linarith
    rcases h16 with ⟨k, hk⟩
    have h17 : k = 0 := by
      by_cases hk1 : k > 0
      · -- Assume k > 0, so k ≥ 1
        have hk2 : k ≥ 1 := by omega
        have hk3 : (k : ℝ) ≥ 1 := by exact_mod_cast hk2
        have hk4 : a + 2 * b ≥ Real.pi / 2 + Real.pi := by
          nlinarith [Real.pi_pos, hk, hk3]
        nlinarith [Real.pi_pos, hk4, h15]
      · -- Assume ¬(k > 0)
        by_cases hk2 : k < 0
        · -- Assume k < 0, so k ≤ -1
          have hk3 : k ≤ -1 := by omega
          have hk4 : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hk3
          have hk5 : a + 2 * b ≤ Real.pi / 2 - Real.pi := by
            nlinarith [Real.pi_pos, hk, hk4]
          nlinarith [Real.pi_pos, hk5, h14]
        · -- Assume k = 0
          omega
    have hk0 : (k : ℝ) = 0 := by exact_mod_cast h17
    rw [hk0] at hk
    nlinarith

  exact h13