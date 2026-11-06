import Mathlib

theorem number_theory_313328 (m : ℕ) :
    ⌊(2 * m + 1) * (Real.sqrt (2 * m + 1)) % 1⌋ = m ↔ m = 0 := by
  have h1 : ⌊(2 * (m : ℝ) + 1) * (Real.sqrt (2 * (m : ℝ) + 1)) % 1⌋ = (0 : ℤ) := by
    have h2 : 0 ≤ (2 * (m : ℝ) + 1) * (Real.sqrt (2 * (m : ℝ) + 1)) % 1 := by
      simp
    have h3 : (2 * (m : ℝ) + 1) * (Real.sqrt (2 * (m : ℝ) + 1)) % 1 < 1 := by
      simp
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try linarith
  constructor
  · -- Forward: if ⌊(...)⌋ = m, then m = 0
    intro h
    have h3 : (0 : ℤ) = m := by linarith [h1, h]
    have h4 : m = 0 := by omega
    assumption
  · -- Backward: if m = 0, then ⌊(...)⌋ = m
    intro h
    rw [h] 
    norm_num [h1]