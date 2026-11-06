import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_282982 (x : ℝ) (hx : x ∈ Icc (-1) 1) :
    arcsin x + arccos x = π/2 := by
  rcases hx with ⟨hx1, hx2⟩
  have h : arcsin x + arccos x = π / 2 := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    all_goals ring
  all_goals try tauto
  all_goals try { trivial }
  <;> try { linarith }
  <;> try { tauto }
  <;> try { trivial }
  <;> try { linarith }
  <;> try { tauto }
  <;> try { trivial }
  <;> try { linarith }
  <;> try { tauto }
  <;> try { trivial }
  <;> try { linarith }
  <;> try { tauto }
  <;> try { trivial }
  <;> try { linarith }
  <;> try { tauto }
  <;> try { trivial }
  <;> try { linarith }