import Mathlib

open Finset

/- Is it possible to divide the integers 1 to 33 into 11 disjoint groups of three elements each, such that in each group, one of the elements is the sum of the other two?-/
theorem logic_and_puzzles_4212 (r s : Finset ℕ) (hr : r = Icc 1 33) (_ : s = range 11) {t : ℕ → Finset ℕ}
    (hf : (s : Set ℕ).PairwiseDisjoint t) (h : disjiUnion s t hf = r)
    (hti : ∀ i ∈ s, ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ (t i) = {x, y, z} ∧ x + y = z) :
    False := by
  -- sum of {1,2,...,33} can be calculated by summing all 11 parts
  have H : ∑ i ∈ s.disjiUnion t hf, i = ∑ i ∈ s, ∑ j ∈ t i, j := sum_disjiUnion s t hf
  rw [h] at H
  -- We can deduce sum of all 11 parts is even.
  -- Because sum of every part {x,y,z} is x+y+z=2z.
  have : ¬Odd (∑ i ∈ r, i) := by
    rw [Nat.not_odd_iff_even, H]
    apply even_sum
    intro i hi
    specialize hti i hi
    rcases hti with ⟨x, y, z, hti⟩
    use x + y
    rw [hti.2.2.2.1]
    nth_rw 2 [hti.2.2.2.2]
    rw [sum_insert (by simp; exact ⟨hti.1, hti.2.1⟩)]
    rw [sum_pair hti.2.2.1]
    ring
  -- On the other hand, sum of {1,2,...,33} is odd.
  have : Odd (∑ i ∈ r, i) := hr ▸ by decide
  -- Hence, we have a contradiction.
  contradiction
