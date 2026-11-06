import Mathlib

/- We give a sufficient condition for a natural number to be the $k^{\mathrm{th}}$ element of a sequence. -/
lemma lemma_1 {p : ℕ → Prop} [DecidablePred p] {n k : ℕ} (H : p n ∧ Nat.count p n = k) : Nat.nth p k = n := by
  rw [← H.2, Nat.nth_count H.1]

/- Let $d$ be a non-zero digit (a natural number from 1 to 9). Determine the $d^{\mathrm{th}}$ positive natural number $x$ such that the decimal representation of $x$ contains the digit $d$. Show that this number is $11d-10$. -/
theorem number_theory_634703 {d : ℕ} (hd : 1 ≤ d ∧ d ≤ 9) :
    Nat.nth (d ∈ Nat.digits 10 ·) (d - 1) = 11 * d - 10 := by
  -- We apply the lemma.
  apply lemma_1
  -- We rewrite the condition that `d` is a non-zero digit to be a membership in the interval [1, 10).
  rw [← Finset.mem_Icc] at hd
  -- Let's use `decide` to check all possible cases of `d`.
  decide +revert +native