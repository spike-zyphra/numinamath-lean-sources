import Mathlib

theorem algebra_142736 (f1 f2 : ℝ → ℝ)
    (hf1 : f1 = fun t => 2 ^ t) (hf2 : f2 = fun t => 2 ^ (t + 3)) :
    ∃ S, S > 0 ∧ ∀ t, f1 t * 4 + f2 t = 2 ^ (t + 2) * S := by
  use 3
  constructor
  · norm_num
  · intro t
    rw [hf1, hf2]
    have h1 : (2: ℝ) ^ t * 4 + (2: ℝ) ^ (t + 3) = (3: ℝ) * (2: ℝ) ^ (t + 2) := by
      have h2 : (2: ℝ) ^ (t + 3) = (2: ℝ) ^ (t + 2) * 2 := by
        rw [show t + 3 = (t + 2) + (1: ℝ) by ring]
        rw [Real.rpow_add]
        norm_num
        all_goals linarith
      have h3 : (2: ℝ) ^ t * 4 = (2: ℝ) ^ (t + 2) := by
        rw [show (t + 2: ℝ) = t + (2: ℝ) by ring]
        rw [Real.rpow_add]
        norm_num
        all_goals linarith
      rw [h3, h2]
      ring_nf
      <;> simp [Real.rpow_add]
      <;> ring_nf
      <;> norm_num
      all_goals linarith
    simp [h1]
    <;> ring_nf
    <;> norm_num