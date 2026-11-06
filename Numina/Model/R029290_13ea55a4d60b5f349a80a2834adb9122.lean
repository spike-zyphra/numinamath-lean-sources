import Mathlib

open Real Set

theorem inequalities_214303 :
    { (x, y) | 2011 * cos (2 * x ^ 2 - y) ≥ x ^ 2 + 2011 } =
    { (x, y) | ∃ k : ℤ, x = 0 ∧ y = 2 * k * π} := by
  ext ⟨x, y⟩ 
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First, prove that if `(x, y)` satisfies the inequality, then `(x, y)` is in the second set.
    intro h
    have h1 : -1 ≤ cos (2 * x ^ 2 - y) ∧ cos (2 * x ^ 2 - y) ≤ 1 := by
      constructor
      · -- Show that -1 ≤ cos (2 * x ^ 2 - y)
        linarith [neg_one_le_cos (2 * x ^ 2 - y)]
      · -- Show that cos (2 * x ^ 2 - y) ≤ 1
        linarith [cos_le_one (2 * x ^ 2 - y)]
    have h2 : x ^ 2 ≤ (0 : ℝ) := by
      nlinarith [h, h1.1, h1.2, Real.cos_le_one (2 * x ^ 2 - y)]
    have hx1 : x = 0 := by
      nlinarith [sq_nonneg x, h2]
    have hx0 : x = 0 := hx1
    rw [hx0] at h
    have h3 : cos (2 * (0 : ℝ) ^ 2 - y) ≥ 1 := by
      nlinarith [h, Real.neg_one_le_cos (2 * (0 : ℝ) ^ 2 - y), Real.cos_le_one (2 * (0 : ℝ) ^ 2 - y)]
    have h4 : cos (2 * (0 : ℝ) ^ 2 - y) = cos y := by
      have h : 2 * (0 : ℝ) ^ 2 - y = -y := by
        ring
      rw [h]
      have h5 : cos (-y) = cos y := by
        rw [cos_neg]
      linarith [h5]
    have h5 : cos y ≥ 1 := by
      nlinarith [h3, h4, Real.neg_one_le_cos y, Real.cos_le_one y]
    have h5' : cos y = 1 := by
      nlinarith [Real.cos_le_one y, Real.neg_one_le_cos y, h5]
    have h6 : ∃ k : ℤ, y = 2 * k * Real.pi := by
      rw [cos_eq_one_iff] at h5'
      rcases h5' with ⟨k, hk⟩
      refine ⟨k, by linarith [hk]⟩
    rcases h6 with ⟨k, hk⟩
    refine ⟨k, by simp [hx1, show y = 2 * k * π by linarith [hk] ]⟩
  · -- Second direction: right side implies inequality holds.
    intro h
    rcases h with ⟨k, hx0, hy⟩
    have hx00 : x = 0 := hx0
    rw [hx00]
    have hy1 : cos (2 * (0 : ℝ) ^ 2 - y) = 1 := by
      have h1 : 2 * (0 : ℝ) ^ 2 - y = -y := by
        ring
      have h2 : cos (2 * (0 : ℝ) ^ 2 - y) = cos y := by
        rw [h1]
        rw [cos_neg]
      have h3 : cos y = 1 := by
        rw [show y = 2 * k * Real.pi by 
          simpa using hy
        ]
        have h4 : cos (2 * k * Real.pi) = 1 := by
          have h6 : cos (2 * k * Real.pi) = 1 := by
            have : 2 * k * Real.pi = (k : ℝ) * (2 * Real.pi) := by ring
            rw [this]
            have h7 : cos ((k : ℝ) * (2 * Real.pi)) = 1 := by
              have h8 : cos ((k : ℝ) * (2 * Real.pi)) = 1 := by 
                have h9 : (k : ℝ) * (2 * Real.pi) = (k : ℝ) * (2 * Real.pi) := by ring
                rw [h9]
                have h10 : cos ((k : ℝ) * (2 * Real.pi)) = 1 := by
                  exact Real.cos_int_mul_two_pi k
                linarith
              linarith
            linarith
          linarith
        linarith [h4]
      linarith [h2, h3]
    nlinarith [Real.cos_le_one (2 * (0 : ℝ) ^ 2 - y), Real.neg_one_le_cos (2 * (0 : ℝ) ^ 2 - y), hy1, Real.pi_pos ]