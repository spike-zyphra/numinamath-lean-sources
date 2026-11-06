import Mathlib

/- Find the smallest positive integer $\mathrm{n}$ so that a cube with side $\mathrm{n}$ can be divided into 1996 cubes each with side a positive integer. -/
theorem number_theory_604704 :
  IsLeast {x | 0 < x ∧ ∃ (f : ℕ → ℕ), (∀ i, 1 ≤ f i) ∧ x^3 = ∑ i ∈ Finset.range 1996, (f i)^3} 13 := by
  -- packing the cubes together to form a $13 \\times 13 \\times 13$ cube is trivial, buy not easy to formalize in lean.
  
  constructor
  . simp
    let f : ℕ → ℕ := fun i => if i = 0 then 5 else if i ≤ 11 then 2 else 1
    use f
    constructor
    . intro i
      unfold f
      split_ifs
      . norm_num
      . norm_num
      . norm_num

    . unfold f
      simp
      native_decide

  . simp [lowerBounds]
    intro x hx f hf heq

    have : ∑ i ∈ Finset.range 1996, 1 ≤ ∑ i ∈ Finset.range 1996, f i ^ 3 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [show 1 = 1 ^ 3 by omega]
      apply Nat.pow_le_pow_left (hf i)

    rw [← heq] at this
    simp at this
    contrapose this
    have : x ≤ 12 := by omega
    have := Nat.pow_le_pow_left this 3
    omega
    