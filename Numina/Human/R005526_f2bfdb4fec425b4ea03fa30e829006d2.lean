import Mathlib

open Finset Nat

/- How many positive integers less than or equal to 240 can be expressed as a sum of distinct factorials? Consider 0 ! and 1 ! to be distinct. -/
theorem number_theory_608658 :
    Set.encard {n : ℕ | 0 < n ∧ n ≤ 240 ∧ ∃ S : Finset ℕ, ∑ i ∈ S, i ! = n} = 39 := by
  -- It suffices to show that the set is equal to a Finset.
  -- So that we can compute the cardinality by `native_decide`.
  suffices H : {n : ℕ | 0 < n ∧ n ≤ 240 ∧ ∃ S : Finset ℕ, ∑ i ∈ S, i ! = n} = ((range 6).powerset.image (fun S => ∑ i ∈ S, i !)).filter (fun n => 0 < n ∧ n ≤ 240) by
    rw [H, Set.encard_coe_eq_coe_finsetCard]
    native_decide
  -- The key observation is that if `S` satisfies `∑ i ∈ S, i ! = n`, then `S` must not contain any number greater than or equal to 6.
  -- So it is a subset of `range 6`.
  ext n
  simp
  constructor
  . rintro ⟨h₁, h₂, S, h₃⟩
    refine ⟨⟨S, ?_, h₃⟩, h₁, h₂⟩
    intro x hx
    simp
    have h₄ := single_le_sum (f := factorial) (s := S) (by simp) hx
    contrapose! h₄
    -- If `x ≥ 6`, then `n = ∑ i ∈ S, i ! ≥ x! ≥ 6! > 240`, contradiction.
    calc ∑ i ∈ S, (i !)
      _ = n := h₃
      _ ≤ 240 := h₂
      _ < 6! := by simp [factorial]
      _ ≤ x ! := factorial_le h₄
  . rintro ⟨⟨S, hS, h₃⟩, h₁, h₂⟩
    exact ⟨h₁, h₂, S, h₃⟩
