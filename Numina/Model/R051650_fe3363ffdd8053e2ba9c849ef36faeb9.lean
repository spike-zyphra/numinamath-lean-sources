import Mathlib

open Real

theorem number_theory_95361 (p : ℕ → ℝ) (hp : ∀ d, p d = logb 10 (d + 1) - logb 10 d) :
    p 2 = 1 / 2 * (∑ i ∈ Finset.Icc 4 8, p i) := by
  have hp2 : p 2 = logb 10 3 - logb 10 2 := by 
    specialize hp 2
    norm_num at hp ⊢
    linarith
  have hsum : ∑ i in Finset.Icc 4 8, p i = (logb 10 9 - logb 10 4) := by 
    simp [Finset.sum_Icc_succ_top, hp 4, hp 5, hp 6, hp 7, hp 8]
    all_goals norm_num
    <;> ring_nf <;> simp [logb]
    <;> ring_nf
  rw [hp2, hsum]
  have h1 : logb 10 9 = 2 * logb 10 3 := by 
    calc
      logb 10 9 = logb 10 (3 ^ 2) := by norm_num
      _ = 2 * logb 10 3 := by simp [logb_pow]
  have h2 : logb 10 4 = 2 * logb 10 2 := by 
    calc 
      logb 10 4 = logb 10 (2 ^ 2) := by norm_num
      _ = 2 * logb 10 2 := by simp [logb_pow]
  rw [h1, h2]
  <;> ring_nf <;> simp [logb]
  <;> ring_nf