import Mathlib

open Nat
/-
Find the smallest positive integer $n$ for which

$$
1!2!\cdots(n-1)!>n!^{2}
$$
-/
theorem number_theory_609900 :
  IsLeast {n : ℕ| 0 < n ∧ (∏ i ∈ Finset.Ico 1 n, i !) > n ! ^ 2} 8 := by
  constructor
  -- $n=8$ gives $34560&gt;448$, so 8 is the integer for which the inequality holds.
  · simp
    decide
  -- so we can rule out all small cases
  · simp [lowerBounds]
    intro a ha ha'
    by_contra!
    interval_cases a
    --  when $n=1 $ or $n=2$, it is easy to see that the inequality does not hold.
    all_goals try simp [Finset.prod_Ico_eq_prod_range] at ha'
    -- $n = 3$ gives $36<6$, so 3 is the integer for which the inequality does not holds.
    · rw [show 3! = 6 by rfl, show ∏ k ∈ Finset.range 2, (1 + k)! = 2 by rfl] at ha'
      simp at ha'
    -- $n = 4$ gives $24^2<12$, so 4 is the integer for which the inequality does not holds.
    · rw [show 4! = 24 by rfl, show 3 = 2 + 1 by omega, Finset.prod_range_succ,
        show ∏ k ∈ Finset.range 2, (1 + k)! = 2 by rfl, show 3! = 6 by rfl] at ha'
      simp at ha'
    -- $n = 5$ gives $120^2<28$, so 5 is the integer for which the inequality does not holds.
    · rw [show 4 = 3 + 1 by omega, Finset.prod_range_succ,
        show 3 = 2 + 1 by omega, Finset.prod_range_succ,
        show ∏ k ∈ Finset.range 2, (1 + k)! = 2 by rfl, show 3! = 6 by rfl] at ha'
      norm_num at ha'
      rw [show 5! = 120 by rfl, show 4! = 24 by rfl] at ha'
      simp at ha'
    -- $n = 6$ gives $720^2<12 * 24 * 120$, so 6 is the integer for which the inequality does not holds.
    · rw [show 5 = 4 + 1 by omega, Finset.prod_range_succ,
        show 4 = 3 + 1 by omega, Finset.prod_range_succ,
        show 3 = 2 + 1 by omega, Finset.prod_range_succ,
        show ∏ k ∈ Finset.range 2, (1 + k)! = 2 by rfl, show 3! = 6 by rfl] at ha'
      norm_num at ha'
      rw [show 6! = 720 by rfl, show 5! = 120 by rfl, show 4! = 24 by rfl] at ha'
      simp at ha'
    -- $n = 7$ gives $5040^2<12 * 24 * 120 * 720$, so 7 is the integer for which the inequality does not holds.
    · rw [show 6 = 5 + 1 by omega, Finset.prod_range_succ,
        show 5 = 4 + 1 by omega, Finset.prod_range_succ,
        show 4 = 3 + 1 by omega, Finset.prod_range_succ,
        show 3 = 2 + 1 by omega, Finset.prod_range_succ,
        show ∏ k ∈ Finset.range 2, (1 + k)! = 2 by rfl, show 3! = 6 by rfl] at ha'
      norm_num at ha'
      rw [show 7! = 5040 by rfl,show 6! = 720 by rfl, show 5! = 120 by rfl, show 4! = 24 by rfl] at ha'
      simp at ha'