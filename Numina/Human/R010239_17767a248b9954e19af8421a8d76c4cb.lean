import Mathlib

/-Bob is trying to decide between two cell phone plans. Plan A has no flat fee, but the user must pay $10$ cents per minute on the phone. Plan B requires a one-time fee of $\$20$, but only requires a payment of $5$ cents per minute on the phone. What is the minimum whole number of minutes Bob has to use the phone for to make Plan B the cheaper plan?-/
theorem algebra_17070 :
    IsLeast {n : ℕ | 10 * n > 2000 + 5 * n} 401 := by
  -- unfold IsLeast
  unfold IsLeast
  -- prove that 401 is in the set
  have _401_in_set: 401 ∈ {n : ℕ | 10 * n > 2000 + 5 * n} := by simp
  use _401_in_set
  refine (le_csInf_iff' ?intro.right.hs).mp ?intro.right.a
  exact Set.nonempty_of_mem _401_in_set
  apply le_csInf
  exact Set.nonempty_of_mem _401_in_set
  simp
  omega
