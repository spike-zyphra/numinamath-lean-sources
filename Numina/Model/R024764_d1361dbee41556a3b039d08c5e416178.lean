import Mathlib

theorem number_theory_259059 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : x * y = 1728) (hgcd : Nat.gcd x y = 12) :
    x = 36 ∧ y = 48 ∨ x = 48 ∧ y = 36 := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx10, hx99⟩
  rcases hy with ⟨hy10, hy99⟩
  have h1 : y = 1728 / x := by
    rw [← hxy]
    field_simp
    all_goals nlinarith
  interval_cases x <;> norm_num [h1] at hxy hgcd ⊢
    <;> try { trivial }
    <;> try { contradiction }
    <;> try { norm_num [Nat.gcd] at hgcd <;> all_goals try { contradiction } }
    <;> try { omega }
    <;> try { nlinarith }
    <;> try { 
      simp [Nat.mul_comm] 
      <;> try { nlinarith } 
      <;> try { contradiction } 
    }
  <;> try { exfalso <;> try { tauto } <;> try { contradiction } <;> try { trivial } }
  <;> try { 
      ring_nf at hxy <;> try { contradiction } 
    }