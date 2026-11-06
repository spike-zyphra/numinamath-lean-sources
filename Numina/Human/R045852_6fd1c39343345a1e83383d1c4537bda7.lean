import Mathlib

/-When flipped, a coin has a probability p of landing heads.
 When flipped twice, it is twice as likely to land on the same side both times as it is to land on each side once.
  What is the larger possible value of p ?-/

/-it's easy to see that the probability of landing on the same side is p ^ 2 + (1 - p) ^ 2,
while the probability of landing on each side is p * (1 - p) + (1 - p) * p  -/
theorem algebra_608737 {p: ℝ} {Prob_same_side Prob_each_side: ℝ → ℝ} (h1: Prob_same_side = fun p => p ^ 2 + (1 - p) ^ 2)
(h2: Prob_each_side = fun p => p * (1 - p) + (1 - p) * p) (h: Prob_same_side p= 2 * Prob_each_side p):
(p ≤ (3 + √3) / 6) ∧ (Prob_same_side ((3 + √3) / 6)= 2 * Prob_each_side ((3 + √3) / 6)) := by
    have eq: √3 ^ 2 = 3 := by   -- equation will be used later --
      norm_num
    constructor
    -- prove the upper any p must be less than or equal to (3 + √3) / 6 --
    simp [h1,h2] at h
    have h3: 6 * p ^ 2 - 6 * p + 1 = 0 := by
      nlinarith [h]
    have eq: 6 * p ^ 2 - 6 * p + 1 = 6 * (p - (3 + √3) / 6) * (p - (3 - √3) / 6) := by
      ring_nf
      rw [eq]
      ring
    rw [eq] at h3
    simp at h3
    rcases h3 with l | l
    . replace l:  p = (3 + √3) / 6 := by
        nlinarith
      rw [l]
    . replace l:  p = (3 - √3) / 6 := by
        nlinarith
      rw [l]
      have ineq: (3 - √3) ≤ (3 + √3) := by
        calc
          3 - √3 ≤ 3 := by norm_num
               _ ≤ 3 + √3 := by norm_num
      nlinarith [ineq]
    -- prove that (3 + √3) / 6 is possible --
    . simp [h1,h2]
      ring_nf
      rw [eq]
      ring