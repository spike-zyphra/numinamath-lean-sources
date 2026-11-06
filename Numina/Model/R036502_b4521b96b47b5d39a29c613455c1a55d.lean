import Mathlib

open Real

theorem algebra_294913 {f : ℝ → ℝ → ℝ} (hf : ∀ x y, x > 0 → y > 0 → (x ≥ y → x * y = y ^ x) ∧ (x < y → x * y = y ^ 2)) :
    f 3 x = 27 ↔ x = 3 ∨ x = 3 * sqrt 3 := by
  constructor
  · -- (→) direction: f 3 x = 27 implies x = 3 ∨ x = 3 * sqrt 3
    intro h
    exfalso
    have h1 := hf 3 3 (by norm_num) (by norm_num)
    norm_num at h1
  · -- (←) direction: x = 3 ∨ x = 3 * sqrt 3 implies f 3 x = 27
    intro h
    rcases h with (rfl | h2)
    · 
      exfalso
      have h1 := hf 3 3 (by norm_num) (by norm_num)
      norm_num at h1
    · 
      exfalso
      have h1 := hf 3 3 (by norm_num) (by norm_num)
      norm_num at h1