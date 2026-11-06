import Mathlib

theorem algebra_199559 (x : ℝ) : ⌊(x - 1) / 2⌋ ^ 2 + 2 * x + 2 = 0 ↔ x = -3 := by 
  constructor
  · -- Assume $⌊(x - 1)/2⌋^2 + 2 * x + 2 = 0$, prove $x = -3$
    intro h
    let n := ⌊(x - 1) / 2⌋
    have h1 : (n : ℝ) ≤ (x - 1) / 2 := by exact_mod_cast (Int.floor_le ((x - 1) / 2))
    have h2 : (x - 1) / 2 < (n + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one ((x - 1) / 2))
    have h3 : (n : ℝ) * 2 + 1 ≤ x := by linarith [h1]
    have h4 : x < (n : ℝ) * 2 + 3 := by linarith [h2]
    have h5 : (n : ℝ) ^ 2 + 2 * x + 2 = (0 : ℝ) := by
      linarith 
    have h6 : x = (- (n : ℝ) ^ 2 / 2 - 1 : ℝ) := by
      nlinarith
    rw [h6] at h3 h4
    have hn1 : n = -2 := by
      have h7 : (n : ℝ) ^ 2 + 4 * (n : ℝ) + 4 ≤ (0 : ℝ) := by nlinarith
      have h8 : (n + 2 : ℝ) ^ 2 ≤ (0 : ℝ) := by nlinarith
      have h9 : (n + 2 : ℝ) = (0 : ℝ) := by nlinarith [sq_nonneg ((n + 2 : ℝ))]
      have hn2 : (n + 2 : ℤ) = 0 := by 
        exact_mod_cast h9
      omega
    have hn2 : (n : ℝ) = (-2 : ℝ) := by 
      exact_mod_cast hn1
    rw [hn2] at h6
    nlinarith
  · -- Assume $x = -3$, prove $⌊(x - 1)/2⌋^2 + 2 * x + 2 = 0$
    intro h
    rw [h]
    norm_num