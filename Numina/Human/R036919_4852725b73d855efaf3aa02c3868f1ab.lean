import Mathlib

/-In a certain sequence the first term is $a_1=2007$ and the second term is $a_2=2008$.  Furthermore, the values of the remaining terms are chosen so that $a_n+a_{n+1}+a_{n+2}=n$ for all $n\ge 1$.  Determine $a_{1000}$.-/
theorem algebra_16619 {a : ℕ → ℝ} (ha1 : a 1 = 2007) (ha2 : a 2 = 2008)
    (han : ∀ n ≥ 1, a n + a (n + 1) + a (n + 2) = n) :
    a 1000 = 2340 := by
  -- To get started, we compute the first ten terms as: \[ 2007, 2008, -4014, 2008, 2009, -4013, 2009, 2010, -4012, 2010, \ldots \]
  -- It appears that each term is 1 greater than the number three terms previous.  We can demonstrate that this will always occur using the given recurrence relation.
  -- We know that $a_n+a_{n+1}+a_{n+2}=n$ and that $a_{n+1}+a_{n+2}+a_{n+3}=n+1$.
  -- Subtracting the former from the latter yields $a_{n+3}-a_n=1$, which is the pattern that we observed.
  have eq : ∀n ≥ 1, a (n + 3) - a n = 1 := by
    intro n hn
    have := han (n + 1) (by linarith)
    specialize han n (by linarith)
    simp at this han
    linarith

  -- Therefore we find that \[ a_1 = 2007, \ a_4=2008, \ a_7=2009, \ldots, a_{1000}=2007+333=\boxed{\mathbf{2340}}. \]
  have : ∀n, a (3 * n + 1) = 2007 + n := by
    intro n
    induction n with
    | zero =>
      simp
      linarith
    | succ n ih =>
      have : 3 * (n + 1) + 1 = (3 * n + 1) + 3 := by linarith
      rw [this]
      specialize eq (3 * n + 1) (by linarith)
      simp
      linarith

  specialize this 333
  simp at this
  linarith
