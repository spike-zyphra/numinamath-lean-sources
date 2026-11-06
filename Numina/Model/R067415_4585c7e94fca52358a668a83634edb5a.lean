import Mathlib

theorem algebra_146649 {P : Polynomial ℂ} (hP : P ≠ 0) (n : ℕ) :
    ∃ a d, ∑ i ∈ Finset.range n, P.derivative.eval^[i] 0 = a + d * i := by 
  use (∑ i ∈ Finset.range n, P.derivative.eval^[i] 0)
  use 0
  simp
  <;> aesop
  <;> try simp_all
  <;> try tauto