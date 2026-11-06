import Mathlib

theorem number_theory_137474 (n : ℕ) :
    ∃ x : Finset.Icc 1 n → ℕ, ∃ y : ℕ,
      ∑ i : Finset.Icc 1 n, (x i)^2 = y^2 := by 
  use fun i => 0
  use 0
  all_goals
    simp
    <;> try { native_decide }
    <;> try { ring_nf }
    <;> try { norm_num }
    <;> try { nlinarith }
    <;> try { linarith }
    <;> try { trivial }