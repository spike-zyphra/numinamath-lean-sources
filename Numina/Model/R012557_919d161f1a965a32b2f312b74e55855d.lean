import Mathlib

theorem number_theory_248217 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : x * y = 1728) (hgcd : Nat.gcd x y = 12) :
    (x = 36 ∧ y = 48) ∨ (x = 48 ∧ y = 36) := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx10, hx99⟩
  rcases hy with ⟨hy10, hy99⟩
  interval_cases x <;> try { 
    omega 
  }
  <;> try { 
    interval_cases y <;> norm_num [Nat.gcd] at hgcd 
      <;> omega 
  }