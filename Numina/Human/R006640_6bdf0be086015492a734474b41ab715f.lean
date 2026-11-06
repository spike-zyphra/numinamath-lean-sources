import Mathlib

open Nat
open ArithmeticFunction

theorem number_theory_639535
    (N0 : ℕ)
    (hN0 : N0 ≥ 4) :
    ¬∃ m ≥ N0, let k := m !; let S := μ k + μ (k + 1) + μ (k + 2); S = 3 ∨ S = -3 := by
  simp --push_neg
  intro m m_ge_0
  suffices μ m ! = 0 by
    have := moebius_eq_or (m ! + 1)
    have := moebius_eq_or (m ! + 2)
    omega
  have : m ≥ 4 := by
    linarith
  have : 4 ∣ m ! := by
    refine dvd_factorial ?_ this
    simp
  rcases this with ⟨n, m_factorial_eq⟩
  rw [m_factorial_eq]
  have : ¬ Squarefree (4 * n) := by
    intro squareFree
    have : Squarefree 4 := by
      exact Squarefree.of_mul_left squareFree
    contradiction
  exact moebius_eq_zero_of_not_squarefree this
