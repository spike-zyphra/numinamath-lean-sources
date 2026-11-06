import Mathlib

open Finset

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

theorem number_theory_4514_2 {a : ℕ → ℤ} {b : ℤ} (ha : ∀ i, IsCoprime (a i) b) (n : ℕ) :
    IsCoprime (∏ i ∈ range n, a i) b := by

  have h1 : ∀ (n : ℕ), IsCoprime (∏ i ∈ range n, a i) b := by 
    intro n 
    induction n with
    | zero =>
      have h1 : IsCoprime (∏ i ∈ range 0, a i) b := by 
        -- The equation simplifies to `1 + 0 * b = 1`, which is true by `ring_nf`.
        simp [IsCoprime, Finset.prod_empty] 
        <;> try { 
          use 1, 0 
          all_goals 
            ring_nf <;> omega 
        }
      exact h1
    | succ n ih =>
      rw [prod_range_succ]
      apply IsCoprime.mul_left
      · -- Show that (∏ i ∈ range n, a i) is coprime with b
        exact ih
      · -- Show that a n is coprime with b
        specialize ha n 
        exact ha
  specialize h1 n 
  simpa using h1