import Mathlib

theorem algebra_170324 {p q : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + p * x + q) :
    abs (f 1) ≥ 1 / 2 ∨ abs (f 2) ≥ 1 / 2 ∨ abs (f 3) ≥ 1 / 2 := by
  by_contra h
  push_neg at h

  have h1 : abs (f 1) < 1 / 2 := h.1
  have h2 : abs (f 2) < 1 / 2 := h.2.1
  have h3 : abs (f 3) < 1 / 2 := h.2.2
  
  have eq1 : f 1 = 1 ^ 2 + p * 1 + q := hf 1
  have eq2 : f 2 = 2 ^ 2 + p * 2 + q := hf 2
  have eq3 : f 3 = 3 ^ 2 + p * 3 + q := hf 3
  
  rw [eq1] at h1
  rw [eq2] at h2
  rw [eq3] at h3
  
  have h1_1 : -1 / 2 < (1 ^ 2 + p * 1 + q) := by linarith [abs_lt.mp h1]
  have h1_2 : (1 ^ 2 + p * 1 + q) < 1 / 2 := by linarith [abs_lt.mp h1]

  have h2_1 : -1 / 2 < (2 ^ 2 + p * 2 + q) := by linarith [abs_lt.mp h2]
  have h2_2 : (2 ^ 2 + p * 2 + q) < 1 / 2 := by linarith [abs_lt.mp h2]

  have h3_1 : -1 / 2 < (3 ^ 2 + p * 3 + q) := by linarith [abs_lt.mp h3]
  have h3_2 : (3 ^ 2 + p * 3 + q) < 1 / 2 := by linarith [abs_lt.mp h3]

  -- Now we have the following constraints:
  -- -1.5 < p + q < -0.5 (from h1_1 and h1_2)
  -- -4.5 < 2p + q < -3.5 (from h2_1 and h2_2)
  -- -9.5 < 3p + q < -8.5 (from h3_1 and h3_2)
  -- Let's derive that these are contradictory
  linarith