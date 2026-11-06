import Mathlib

theorem algebra_245046 (n : ℕ) (h : n > 0) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by 
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero =>
      simp
    | succ n =>
      simp [Finset.sum_range_succ] at ih ⊢
      <;> ring_nf <;> linarith