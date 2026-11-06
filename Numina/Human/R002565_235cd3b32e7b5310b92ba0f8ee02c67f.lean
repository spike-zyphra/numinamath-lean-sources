import Mathlib

/-
PROBLEM: When a certain biased coin is flipped five times, the probability of getting heads exactly once
is not equal to 0 and is the same as that of getting heads exactly twice. Let ij​, in lowest terms, be
the probability that the coin comes up heads in exactly 3 out of 5 flips. Find i+j.
-/

theorem combinatorics_95509 (p : ℚ) (h₀ : p ≠ 0) (h₁ : (1 - p) ≠ 0)
(h₂ : ((Nat.choose 5 1)) *p^1 * (1 - p)^4 = (Nat.choose 5 2) * p^2 * (1 - p)^3) :
(Nat.choose 5 3) * p^3 * (1 - p)^2 = 40 / 243 := by {
  -- Plug in the value of p and conclude. The calculation of p is done afterwards.
  suffices : p = 1 / 3
  rw [this]
  norm_num
  rw [Nat.choose_eq_factorial_div_factorial]
  have : Nat.factorial 5 = 120 := by trivial
  rw [this]
  have : Nat.factorial 3 = 6 := by trivial
  rw [this]
  simp
  norm_num
  trivial
  -- Calculation of p. We cancel factors on both sides until we arrive at 1 - p = 2p. From there,
  -- the conclusion is immediate.
  simp at h₂
  suffices : 1 - p = 2*p
  linarith
  have : Nat.choose 5 2 = 10 := by trivial
  rw [this] at h₂
  calc 1 - p = (5 * p * (1 - p)^3) * (1-p) / (5 * p * (1 - p)^3) := by field_simp
           _ = 5 * p * (1 - p) ^ 4 / (5 * p * (1 - p)^3) := by ring
           _ = 10 * p ^ 2 * (1 - p) ^ 3 / (5 * p * (1 - p)^3) := by rw [h₂]; simp
           _ = 2 * p := by field_simp; ring
}