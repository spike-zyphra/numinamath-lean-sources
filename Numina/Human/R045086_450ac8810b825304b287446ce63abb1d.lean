import Mathlib

open Finset

/- a) Show that if \( a, b, \) and \( c \) are integers with \( (a, b) = (a, c) = 1 \), then \( (a, b c) = 1 \).-/
theorem number_theory_4514_1 {a b c : ℤ} (hab : IsCoprime a b) (hac : IsCoprime a c) :
    IsCoprime a (b*c) := by
  -- 1. Since \( (a, b) = 1 \), there exist integers \( x \) and \( y \) such that \( ax + by = 1 \).
  obtain ⟨x, y, hxy⟩ := hab
  -- 2. Similarly, since \( (a, c) = 1 \), there exist integers \( m \) and \( n \) such that \( am + cn = 1 \).
  obtain ⟨m, n, hmn⟩ := hac
  -- there is a linear combination of a, bc such that aX+bcY=1.
  -- This means that a, bc are coprime.
  have hyb : y*b = 1 + (-x)*a := by linarith
  have hnc : n*c = 1 + (-m)*a := by linarith
  have hynbc : (y*n)*(b*c) = (1 + (-x)*a)*(1 + (-m)*a) := by rw [← hyb, ← hnc]; ac_rfl
  use (x+m-m*x*a), (y*n)
  rw [hynbc]
  ring

/- b) Use mathematical induction to show that if \( a_{1}, a_{2}, \ldots, a_{n} \) are integers, and \( b \) is another integer such that \( (a_{1}, b) = (a_{2}, b) = \cdots = (a_{n}, b) = 1 \), then \( (a_{1} a_{2} \cdots a_{n}, b) = 1 \).-/
theorem number_theory_4514_2 {a : ℕ → ℤ} {b : ℤ} (ha : ∀ i, IsCoprime (a i) b) (n : ℕ) :
    IsCoprime (∏ i ∈ range n, a i) b := by
  -- use mathematical induction on n
  induction' n with n ih
  -- check the base case
  . simpa using isCoprime_one_left
  . rw [prod_range_succ]
    symm
    -- use the conclusion from `number_theory_4514_1`
    apply number_theory_4514_1
    -- use induction hypothesis
    exact ih.symm
    exact (ha n).symm
