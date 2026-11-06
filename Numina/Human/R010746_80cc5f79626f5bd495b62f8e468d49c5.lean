import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic.Linarith

open Finset

/- Fomin D:

There are $n$ integers ( $n>1$ ). It is known that each of them differs from the product of all the others by a number divisible by $n$.

Prove that the sum of the squares of these numbers is divisible by $n$.

# -/

theorem number_theory_184632 {n : ℕ} (hn : n > 1) (a : Fin n → ℤ) (h : ∀ i, a i - ∏ j ∈ univ \ {i}, a j ≡ 0 [ZMOD n]) : ∑ i, (a i)^2 ≡ 0 [ZMOD n] := by
  let P := ∏ j ∈ univ, a j
  -- Show that (a i)^2 is congruent to P mod n
  have mod_eqn (i : Fin n) : (a i)^2 ≡ P [ZMOD n] := by
    -- Use the hypothesis at i
    have h' : a i ≡ ∏ j ∈ univ \ {i}, a j [ZMOD n] := by
      have : a i - ∏ j ∈ univ \ {i}, a j + ∏ j ∈ univ \ {i}, a j ≡ 0 + ∏ j ∈ univ \ {i}, a j [ZMOD n] := Int.ModEq.add_right _ (h i)
      rw [zero_add, sub_add_cancel] at this
      tauto
    -- Rewrite P
    have prod : P = (∏ j ∈ univ \ {i}, a j) * a i := by
      rw [← prod_singleton a i]
      refine Eq.symm (prod_sdiff ?_)
      exact subset_univ {i}
    rw [prod]
    apply Int.ModEq.mul_right (a i)
    simp
    exact h'
  -- Express 0 as a sum
  have : 0 ≡ ∑ i : Fin n, P [ZMOD n] := by
    simp
    rw [Int.modEq_comm, Int.modEq_zero_iff_dvd]
    exact Int.dvd_mul_right (↑n) P
  -- Rewrite 0 as the sum using transitive property
  trans (∑ i : Fin n, P)
  -- Swap the goals to solve the easier one first
  swap
  · exact Int.ModEq.symm this
  rw [Int.modEq_iff_dvd, ← sum_sub_distrib]
  have n_dvd : ∀ i ∈ univ, ↑n ∣ P - (a i)^2 := fun i _ => Int.ModEq.dvd (mod_eqn i)
  exact dvd_sum n_dvd