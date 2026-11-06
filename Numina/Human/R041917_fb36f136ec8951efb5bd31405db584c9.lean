import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith

/-- Desired property for the variable $n$. -/
def P (n : ℕ) : Prop := ∃ c, ∃ x : Fin c → ℕ,
  (∀ k, 0 ≤ x k) ∧
  (∀ k, x k + 2*k = n) ∧
  (∑ k, x k = 2009)

/-- A group of children held a grape-eating contest.
When the contest was over, the winner had eaten $n$ grapes, and the child in $k$-th place had eaten
$n+2-2k$ grapes. The total number of grapes eaten in the contest was $2009$. Find the smallest
possible value of $n$. -/
theorem algebra_738 : P 89 ∧ ∀ n, P n → 89 ≤ n := by
  constructor

  -- $n = 89$ is a valid solution.
  · rw [P]
    use 41
    use (fun k => 89 - 2*k)
    exact ⟨by decide, by decide, by decide⟩

  -- Let's prove that $n = 89$ is the smallest possible solution.
  · intro n hn
    rcases hn with ⟨c, x, h1, h2, h3⟩

    -- Sum the given equation to relate $n$ and $c$.
    have : ∑ k, x k + ∑ k : Fin c, 2 * (k : ℕ) = ∑ k : Fin c, n := by
      rw [←Finset.sum_add_distrib]
      congr
      ext k
      exact h2 k

    have : ∑ k, x k + ∑ k : Fin c, 2 * (k : ℕ) = c * n := by
      rw [Finset.sum_const] at this
      simp at this
      exact this

    have : ∑ k, x k + 2 * ∑ k : Fin c, (k : ℕ) = c * n := by
      rw [Finset.mul_sum, this]

    have : ∑ k, x k + 2 * (c * (c - 1) / 2) = c * n := by
      rw [←this, ←Finset.sum_range_id, ←Fin.sum_univ_eq_sum_range]

    have : ∑ k, x k + c * (c - 1) = c * n := by
      rw [←this]
      congr 1
      rw [Nat.two_mul_div_two_of_even]
      apply Nat.even_mul_pred_self

    -- We get the equation following involving the total number of grapes.
    have : 2009 + c * (c - 1) = c * n := by rw [←h3, this]

    -- There are $6$ divisors of $2009$: $1, 7, 49, 41, 287$ and $2009$.
    have h2009 : Nat.divisors 2009 = {1, 7, 49, 41, 287, 2009} := by
      set_option maxRecDepth 2000 in
      decide

    -- $c$ is a divisor of 2009.
    have hc : c ∣ 2009 := by
      apply (Nat.dvd_add_iff_left (n := c * (c - 1)) (by simp)).mpr
      rw [this]
      simp

    replace hc : c ∈ ({1, 7, 49, 41, 287, 2009} : Finset ℕ) := by
      rw [←h2009, Nat.mem_divisors]
      exact ⟨hc, by decide⟩

    -- The divisors of 2009 are 1, 7, 49, 41, 287 and 2009. These are the only
    -- possible values for $c$.
    replace hc : c = 1 ∨ c = 7 ∨ c = 49 ∨ c = 41 ∨ c = 287 ∨ c = 2009 := by
      simp at hc
      exact hc

    -- Trying each case one by one, we verify that $n = 89$ is the smallest
    -- possible solution.
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) <;> nlinarith