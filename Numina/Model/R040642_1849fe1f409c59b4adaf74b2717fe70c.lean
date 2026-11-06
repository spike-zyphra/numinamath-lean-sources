import Mathlib

open Mathlib

lemma lemma_1 {n : ℕ} (hn : n > 0) (T : ℝ)
  (hsum : T = n * 56) (havg : (n - 1) * 55 = T - 68) :
  T = 728 := by
  have eq1 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast (show (n : ℕ) > 0 by linarith)
  have eq2 : (n : ℝ) = 13 := by
    have eq3 : (n : ℝ) > 0 := eq1
    nlinarith [hsum, havg]
  rw [show (n : ℝ) = 13 by linarith [eq2] ] at hsum
  nlinarith