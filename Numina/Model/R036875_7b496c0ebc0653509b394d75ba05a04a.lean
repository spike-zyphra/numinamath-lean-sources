import Mathlib

open Real Set
open scoped Topology

theorem algebra_16613 :
    {y : ℝ | (y - 2) + (y - 8) ≠ 0} = Iio 5 ∪ Ioi 5 := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · -- Assume $(y - 2) + (y - 8) ≠ 0$ prove $y \in (-\infty, 5) \cup (5, \infty)$
    intro h
    have h1 : (y - 2) + (y - 8) ≠ 0 := h
    have h2 : y ≠ 5 := by
      by_contra h_eq
      have eq : (y - 2) + (y - 8) = 0 := by
        rw [h_eq]
        norm_num
      contradiction
    by_cases h3 : y < 5
    · -- Case y < 5
      left
      exact h3
    · -- Case y ≥ 5
      have h4 : y > 5 := by
        by_contra h5
        push_neg at h5
        have h5 : y = 5 := by linarith
        contradiction
      right
      exact h4
  · -- Assume $y \in (-\infty, 5) \cup (5, \infty)$ prove $(y - 2) + (y - 8) ≠ 0$
    rintro (h | h)
    · -- Case y < 5
      have h1 : y < 5 := h
      have h2 : (y - 2) + (y - 8) ≠ 0 := by
        by_contra h_eq
        have eq : y = 5 := by
          nlinarith
        nlinarith
      exact h2
    · -- Case y > 5
      have h1 : y > 5 := h
      have h2 : (y - 2) + (y - 8) ≠ 0 := by
        by_contra h_eq
        have eq : y = 5 := by
          nlinarith
        nlinarith
      exact h2