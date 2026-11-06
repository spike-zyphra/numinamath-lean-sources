import Mathlib
open Real Set

theorem algebra_9452 {f : ℝ → ℝ} (hf : f = λ x => 3 - 2 * cos (x + π / 4)) :
    IsGreatest (range f) 5 ∧
    ∀ x, f x = 5 ↔ ∃ k : ℤ, x = 2 * k * π + 3 * π / 4 := by
  constructor
  · -- Show 5 is greatest in range
    constructor
    · -- Show 5 is in range
      use (3 * π / 4)
      rw [hf]
      simp
      have hcos : cos (3 * π / 4 + π / 4) = cos π := by ring_nf
      rw [hcos]
      have hcos2 : cos π = -1 := by
        exact cos_pi
      linarith [hcos2]
    · -- Show 5 is the greatest
      intro y
      rintro ⟨x, hx⟩
      rw [hf] at hx
      simp at hx
      have hcos : -1 ≤ cos (x + π / 4) ∧ cos (x + π / 4) ≤ 1 := by
        apply cos_mem_Icc
      nlinarith [hcos.1, hcos.2]
  · -- Show the equivalence
    intro x
    constructor
    · -- Assume f x = 5, prove existence of k
      intro hfx
      rw [hf] at hfx
      simp at hfx
      have hcos : cos (x + π / 4) = -1 := by linarith
      obtain ⟨k, hk⟩ := cos_eq_neg_one_iff.1 hcos
      refine ⟨k, by
        have eq1 : x + π / 4 = π + 2 * k * π := by
          linarith [hk]
        linarith [eq1]
      ⟩
    · -- Assume existence of k, prove f x = 5
      rintro ⟨k, heq⟩
      rw [hf]
      simp at *
      have hcos : cos (x + π / 4) = -1 := by
        rw [show x + π / 4 = (k : ℝ) * (2 * π) + π by
          rw [heq]
          ring_nf
        ]
        have : cos ((k : ℝ) * (2 * π) + π) = cos π := by
          have : (k : ℝ) * (2 * π) + π = π + (k : ℝ) * (2 * π) := by ring_nf
          rw [this]
          have : cos (π + (k : ℝ) * (2 * π)) = cos π := by
            have : π + (k : ℝ) * (2 * π) = π + (k : ℤ) * (2 * π) := by ring_nf
            rw [this]
            rw [cos_add_int_mul_two_pi]
          linarith
        rw [this]
        exact cos_pi
      linarith [hcos]