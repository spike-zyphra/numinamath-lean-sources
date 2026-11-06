import Mathlib

/-- Show that the sum of the first $n$ odd integers equals $n^{2}$.-/
theorem algebra_4037 (n : ℕ) :
  (∑ i in Finset.range (n), (2*i + 1)) = (n^2) := by
    -- Classify and discuss $n=0$ or $n=k.succ$
    cases n
    -- if $n=0$, it is easy to check.
    simp
    rename_i k
    rw [Finset.range_succ]
    simp
    -- if $n=k.succ$, use the hypothesis and simplify.
    rw [algebra_4037 k]
    linarith
