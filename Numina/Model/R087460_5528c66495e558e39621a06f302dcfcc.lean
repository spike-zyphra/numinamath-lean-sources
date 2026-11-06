import Mathlib

theorem number_theory_200771 : ∃ n, ∀ i ∈ Finset.range 35, ⌊Real.sqrt (n + i)⌋ = 17 := by
  use 289
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 : (289 + i : ℝ) ≥ (17 : ℝ) ^ 2 := by
    have h2 : (i : ℝ) ≥ 0 := by
      exact_mod_cast (show (i : ℕ) ≥ 0 by omega)
    have h3 : (289 + i : ℝ) ≥ (289 : ℝ) := by
      linarith
    have h4 : (289 : ℝ) = (17 : ℝ) ^ 2 := by norm_num
    linarith [h4]
  have h5 : (289 + i : ℝ) < (18 : ℝ) ^ 2 := by
    have h6 : (i : ℝ) < (35 : ℝ) := by
      exact_mod_cast (show i < 35 by linarith)
    have h7 : (289 + i : ℝ) < (324 : ℝ) := by
      nlinarith
    have h8 : (18 : ℝ) ^ 2 = (324 : ℝ) := by norm_num
    nlinarith [h8]
  have h7 : 17 ≤ Real.sqrt (289 + i : ℝ) := by
    have h8 : Real.sqrt ((17 : ℝ) ^ 2) ≤ Real.sqrt ((289 + i : ℝ))
    · apply Real.sqrt_le_sqrt
      nlinarith
    have h9 : Real.sqrt ((17 : ℝ) ^ 2) = (17 : ℝ) := by
      rw [Real.sqrt_sq]
      all_goals linarith
    linarith [h8, h9]
  have h8 : Real.sqrt (289 + i : ℝ) < 18 := by
    have h9 : Real.sqrt ((289 + i : ℝ)) < Real.sqrt ((18 : ℝ) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    have h10 : Real.sqrt ((18 : ℝ) ^ 2) = (18 : ℝ) := by
      rw [Real.sqrt_sq]
      all_goals linarith
    linarith [h9, h10]
  have h9 : ⌊Real.sqrt (289 + i : ℝ)⌋ = 17 := by
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith [h7, h8]
  exact h9