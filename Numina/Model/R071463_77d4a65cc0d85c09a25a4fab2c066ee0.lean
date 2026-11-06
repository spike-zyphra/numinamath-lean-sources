import Mathlib

theorem algebra_94086 {a b : ℝ} (y : ℝ → ℝ) (hy : y = fun x => (x - a) ^ 2 + (x - b) ^ 2) :
    IsMinOn y (Set.univ : Set ℝ) ((a + b) / 2) := by 
  unfold IsMinOn
  intro x 
  simp [hy]
  have h1 : ((x - a) ^ 2 + (x - b) ^ 2) - (( (a + b) / 2 - a ) ^ 2 + ( (a + b) / 2 - b ) ^ 2) = 2 * (x - (a + b)/2)^2 := by 
    ring_nf
  have h2 : ((x - a) ^ 2 + (x - b) ^ 2) ≥ (( (a + b) / 2 - a ) ^ 2 + ( (a + b) / 2 - b ) ^ 2) := by 
    have h' : ((x - a) ^ 2 + (x - b) ^ 2) - (( (a + b) / 2 - a ) ^ 2 + ( (a + b) / 2 - b ) ^ 2) ≥ 0 := by
      rw [h1]
      have h3 : 2 * (x - (a + b)/2)^2 ≥ 0 := mul_nonneg (by norm_num) (pow_two_nonneg _)
      linarith
    linarith
  linarith