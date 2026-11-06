import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_144043 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => a * cos (x / 2))
  (hA : f (π / 2) = sqrt 2) :
  a = 2 ∧ ∀ x, f x = 0 ↔ ∃ k : ℤ, x = π + 2 * k * π := by
  have h1 : f (π / 2) = a * cos ((π / 2) / 2) := by
    rw [hf]
  have h2 : (π / 2 : ℝ) / 2 = π / 4 := by ring
  have h3 : cos ((π / 2) / 2) = Real.sqrt 2 / 2 := by
    rw [show (π / 2 : ℝ) / 2 = π / 4 by ring]
    have hcos : cos (π / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    linarith [hcos]
  rw [h1, h3] at hA
  have ha : a = 2 := by
    have h8 : Real.sqrt 2 > 0 := by
      positivity
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  have h9 : ∀ x, f x = 0 ↔ ∃ k : ℤ, x = π + 2 * k * π := by
    intro x
    have hfx : f x = a * cos (x / 2) := by
      rw [hf]
    rw [hfx, ha]
    constructor
    · -- Forward direction: If 2 * cos(x/2) = 0, then ∃ k, x = π + 2*k*π
      intro h
      have h10 : cos (x / 2) = 0 := by
        nlinarith
      obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 h10
      use k
      have hk' : x / 2 = Real.pi / 2 + ↑k * Real.pi := by
        linarith [hk]
      have h6 : x = Real.pi + 2 * (↑k : ℝ) * Real.pi := by
        have eq1 : x / 2 = Real.pi / 2 + ↑k * Real.pi := by
          linarith [hk']
        have eq2 : x = 2 * (x / 2) := by ring
        rw [eq2, eq1]
        ring
      exact_mod_cast h6
    · -- Backward direction: If ∃ k, x = π + 2*k*π, then 2 * cos(x/2) = 0
      intro h
      rcases h with ⟨k, hk⟩
      have hk' : (x : ℝ) = Real.pi + 2 * (↑k : ℝ) * Real.pi := by
        exact_mod_cast hk
      have h10 : cos (x / 2) = 0 := by
        have h10k : x / 2 = Real.pi / 2 + (↑k : ℝ) * Real.pi := by
          have eq1 : x = Real.pi + 2 * (↑k : ℝ) * Real.pi := by
            linarith [hk']
          have eq2 : x / 2 = (Real.pi + 2 * (↑k : ℝ) * Real.pi) / 2 := by
            rw [eq1]
          field_simp at eq2 ⊢
          linarith [eq2]
        rw [h10k]
        have hk55 : sin (↑k * Real.pi) = 0 := by
          have h555 : sin (↑k * Real.pi) = 0 := by
            have h444 : ↑k * Real.pi = (↑k : ℝ) * Real.pi := by ring
            rw [h444]
            simp [Real.sin_int_mul_pi]
          linarith [h555]
        have hk4k : cos (Real.pi / 2 + ↑k * Real.pi) = 0 := by
          have hk4k1 : cos (Real.pi / 2 + ↑k * Real.pi) = -sin (↑k * Real.pi) := by
            rw [cos_add]
            simp [sin_pi_div_two, cos_pi_div_two, sin_pi, cos_pi]
            all_goals ring_nf <;> simp [neg_mul, mul_neg]
            all_goals linarith
          rw [hk4k1, hk55]
          all_goals linarith
        linarith
      nlinarith [Real.pi_pos]
  constructor
  · exact ha
  · exact h9