import Mathlib

/- 4. Given the sequence $\left\{a_{n}\right\}(n \geqslant 1)$ satisfies $a_{n+2}=$ $a_{n+1}-a_{n}$ and $a_{2}=1$. If the sum of the first 1999 terms of this sequence is 2000, then the sum of the first 2000 terms equals ( ).
(A) 1999
(B) 2000
(C) 2001
(D) 2002 -/
theorem algebra_296821 {a : ℕ → ℤ} (h : ∀ n, a (n + 2) = a (n + 1) - a n) (ha : a 2 = 1)
    (hsum : ∑ i in Finset.Icc 1 1999, a i = 2000) :
    ∑ i in Finset.Icc 1 2000, a i = 2001 := by
  -- Prove that the sequence has a period of 6
  -- (i.e., a(n+6) = a(n) for all n)
  have period6 : ∀ n, a (n + 6) = a n := by
    intro n
    -- Apply the recurrence relation multiple times
    have h1 := h n
    have h2 := h (n + 1)
    have h3 := h (n + 2)
    have h4 := h (n + 3)
    have h5 := h (n + 4)
    have h6 := h (n + 5)
    simp at h1 h2 h3 h4 h5 h6
    -- Use linear arithmetic to prove the periodicity
    linarith

  -- Express the sum of 2000 terms as the sum of 1999 terms plus a(2000)
  have sum_2000 : ∑ i in Finset.Icc 1 2000, a i = ∑ i in Finset.Icc 1 1999, a i + a 2000 := by
    rw [Finset.sum_Icc_succ_top (by norm_num)]

  -- Prove that a(2000) = a(2) using the periodicity property
  have a2000_eq_a2 : a 2000 = a 2 := by
    have h2000 : a 2000 = a 2 := by
      norm_num [period6]
    exact h2000

  -- Substitute the sum of 1999 terms and simplify
  rw [sum_2000, hsum]

  -- Since a(2000) = a(2) = 1, the final sum is 2000 + 1 = 2001
  have ha2000 : a 2000 = 1 := by
    rw [a2000_eq_a2, ha]
  linarith [ha2000]
