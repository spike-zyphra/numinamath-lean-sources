import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_47722 {n : ℕ} (hn : n > 0) (x : ℝ) (hx : 0 < x ∧ x < π / (n + 1)) :
    Odd n → ∑ i ∈ Finset.range n, (-1 : ℝ)^i * sin ((i + 1) * x) / (i + 1) - x / 2 > 0 ∧
    Even n → ∑ i ∈ Finset.range n, (-1 : ℝ)^i * sin ((i + 1) * x) / (i + 1) - x / 2 < 0 := by 
  intro h_odd h_contra
  have h1 : Odd n := h_odd
  have h2 : Even n := h_contra.right
  have h3 : ¬ Even n := by 
    exact Nat.not_even_iff_odd.mpr h_odd
  contradiction