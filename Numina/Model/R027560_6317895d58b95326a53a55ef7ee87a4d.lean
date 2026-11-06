import Mathlib

theorem number_theory_105794 (S : Finset ℤ) (hS : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≥ 10)
    (hS1 : ∃ x y z, x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ x > y ∧ y > z ∧ x^2 + y^2 + z^2 < 3000000)
    (hS2 : ∃ x y z, x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ x < y ∧ y < z ∧ x^2 + y^2 + z^2 < 3000000) :
    S.card ≤ 202 := by
  have h5 := hS1
  rcases h5 with ⟨x1, y1, z1, hx1, hy1, hz1, h4, h5, h6⟩
  specialize hS x1 hx1 x1 hx1
  norm_num at hS
  all_goals 
    try { contradiction }
    <;> try { omega }