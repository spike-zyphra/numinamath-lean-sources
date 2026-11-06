import Mathlib

/- The product of 50 consecutive integers is zero and the sum of these numbers is positive.
  What is the smallest value that this sum can assume? -/
theorem number_theory_253102 :
  IsLeast
    {s | ∃ n : ℤ, ∏ i ∈ Finset.range 50, (n + i) = 0 ∧
                  ∑ i ∈ Finset.range 50, (n + i) > 0 ∧
                  ∑ i ∈ Finset.range 50, (n + i) = s
    } 25 := by
  constructor
  · -- Show 25 is in the set
    use -24
    decide
  · -- Show 25 is the least element in the set
    intro s ⟨n, _, hsum_pos, hsum_eq⟩
    have h1 : ∑ i ∈ Finset.range 50, (n + i) = 50 * n + 1225 := by
      simp [Finset.sum_add_distrib]
      ring_nf
    omega
