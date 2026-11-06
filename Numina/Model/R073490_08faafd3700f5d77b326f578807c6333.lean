import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_68553 (a b : ℝ) (f : ℝ → ℝ) (hf : f = λ x => x^2 + a * x + b)
  (m : ℝ) (hm : |f m| ≤ 1 / 4 ∧ |f (m + 1)| ≤ 1 / 4) :
  0 ≤ a^2 - 4 * b ∧ a^2 - 4 * b ≤ 2 := by
  have h1 : -1 / 4 ≤ f m := by linarith [abs_le.mp hm.1]
  have h2 : f m ≤ 1 / 4 := by linarith [abs_le.mp hm.1]
  have h3 : -1 / 4 ≤ f (m + 1) := by linarith [abs_le.mp hm.2]
  have h4 : f (m + 1) ≤ 1 / 4 := by linarith [abs_le.mp hm.2]
  have h5 : -1 / 4 ≤ m^2 + a * m + b := by
    rw [hf] at h1
    simpa using h1
  have h6 : m^2 + a * m + b ≤ 1 / 4 := by
    rw [hf] at h2
    simpa using h2
  have h7 : -1 / 4 ≤ (m + 1)^2 + a * (m + 1) + b := by
    rw [hf] at h3
    simpa using h3
  have h8 : (m + 1)^2 + a * (m + 1) + b ≤ 1 / 4 := by
    rw [hf] at h4
    simpa using h4
  constructor
  · -- Proof that 0 ≤ a^2 - 4 * b
    nlinarith [sq_nonneg (m), sq_nonneg (m + 1), sq_nonneg (a - 2 * m - 1), sq_nonneg ((m + 1 / 2) * 2 + a * 2), sq_nonneg (m * (m + 1 / 2)), sq_nonneg ((m + 1) * (m + 1 / 2)), sq_nonneg (a + 2 * m + 1)]
  · -- Proof that a^2 - 4 * b ≤ 2
    nlinarith [sq_nonneg (m + 1 / 2), sq_nonneg (a + 2 * m + 1), sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - 2 * m), sq_nonneg ((m * 2) + a), sq_nonneg ((m * 2) + a), sq_nonneg ((m + 1) * 2 + a)]