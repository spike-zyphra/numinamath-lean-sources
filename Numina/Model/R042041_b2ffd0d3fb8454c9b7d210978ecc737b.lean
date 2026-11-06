import Mathlib

theorem number_theory_116341 (M P : Fin 2010 → ℕ)
    (hM : ∀ n, M n = ∑ i in Finset.range n, (2 * i + 2))
    (hP : ∀ n, P n = M n % 10) :
    ∑ i in Finset.range 2010, P i = 4020 := by 
  simp_all [Finset.sum_congr, hM, hP]
  <;> try native_decide
  <;> try native_decide
  <;> try native_decide
  <;> try native_decide
  <;> try native_decide
  <;> try native_decide
  <;> try native_decide