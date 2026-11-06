import Mathlib

/- A book is said to have $n$ leaves if it is composed of $n$ pieces of paper. On the other hand, the number of pages is twice the number of leaves because each side of a piece of paper is defined as a page.

If the number of pages in a book is $3$ more than a multiple of $7$, and the number of leaves is greater than $100$, then what is the smallest possible number of leaves? -/
theorem number_theory_22925 : IsLeast {leaves : ℕ | ∃ pages : ℕ, pages = 2 * leaves ∧ ∃ k : ℕ, pages = 7 * k + 3 ∧ 100 < leaves} 103 := by
  constructor
  · -- $103$ is a possible value
    use 206
    norm_num
    use 29
  · -- $103$ is the least such
    intro leaves leavesin
    rcases leavesin with ⟨pages, hl, k, hp, lge⟩
    by_contra contra
    -- for otherwise, $leaves = 100, 101, 102$, all leading to contradictions
    apply congrArg (fun (x : ℕ) ↦ (x : ZMod 7)) at hp
    have eq : (7 : ZMod 7) = 0 := by
      exact rfl
    simp only [hl, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, eq, zero_mul, zero_add] at hp
    interval_cases leaves
    any_goals
    contradiction