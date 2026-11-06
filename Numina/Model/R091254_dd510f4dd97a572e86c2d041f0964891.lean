import Mathlib

theorem number_theory_318158 (n : ℕ) (hn : n > 100) :
    (Nat.floor ((Real.sqrt (n^2 + 3 * n + 1)) * 100)) % 100 = 49 := by
  have h1 : (n : ℝ) > (100 : ℝ) := by exact_mod_cast hn
  have h2 : (Real.sqrt (n^2 + 3 * n + 1)) < (n + 150 / 100 : ℝ) := by
    have h3 : (Real.sqrt (n^2 + 3 * n + 1)) ^ 2 = (n^2 + 3 * n + 1 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (n^2 + 3 * n + 1 : ℝ), show (n + 150 / 100 : ℝ) ^ 2 = (n : ℝ) ^ 2 + 3 * (n : ℝ) + (225 / 100 : ℝ) by ring_nf, show (n : ℝ)^2 + 3 * (n : ℝ) + 1 < (n + 150 / 100 : ℝ)^2 by nlinarith ]
  have h4 : (n + 149 / 100 : ℝ) < (Real.sqrt (n^2 + 3 * n + 1)) := by
    have h5 : (Real.sqrt (n^2 + 3 * n + 1)) ^ 2 = (n^2 + 3 * n + 1 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (n^2 + 3 * n + 1 : ℝ), show (n + 149 / 100 : ℝ) ^ 2 = (n : ℝ) ^ 2 + (298 / 100 : ℝ) * (n : ℝ) + (22201 / 10000 : ℝ) by ring_nf, show (n + 149 / 100 : ℝ) ^ 2 < (n^2 + 3 * n + 1 : ℝ) by nlinarith ]
  have h5 : (Real.sqrt (n^2 + 3 * n + 1)) * 100 > (100 * (n : ℝ) + 149) := by
    have h6 : Real.sqrt (n^2 + 3 * n + 1 : ℝ) > (n + 149 / 100 : ℝ) := by linarith [h4]
    linarith
  have h7 : (Real.sqrt (n^2 + 3 * n + 1 : ℝ)) * 100 < (100 * (n : ℝ) + 150) := by
    have h8 : Real.sqrt (n^2 + 3 * n + 1 : ℝ) < (n + 150 / 100 : ℝ) := by linarith [h2]
    linarith
  have h8 : Nat.floor ((Real.sqrt (n^2 + 3 * n + 1)) * 100) = 100 * n + 149 := by
    simp [Nat.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  calc
    (Nat.floor ((Real.sqrt (n^2 + 3 * n + 1)) * 100)) % 100
        = (100 * n + 149) % 100 := by rw [h8]
    _ = 49 := by omega