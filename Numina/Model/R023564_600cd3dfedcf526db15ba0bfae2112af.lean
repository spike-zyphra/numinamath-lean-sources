import Mathlib

theorem number_theory_230566 (a b c p : ℤ) (hp : Prime p) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      (a * x ^ 2 + b * y ^ 2 + c * z ^ 2) ≡ 0 [ZMOD p] := by
  use p, 0, 0
  constructor
  · -- Show that x is non-zero
    left
    by_contra h
    have h1 : p = (0 : ℤ) := by linarith
    rw [h1] at hp
    -- A prime number can't be zero
    norm_num at hp
    -- norm_num at hp will lead to contradiction
  · -- Show congruence
    simp [Int.ModEq, Int.emod, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
    <;> ring_nf <;> norm_num
    <;> try { 
      have h : p ∣ p := by 
        simp
      have : p ∣ a * p ^ 2 := by 
        use a * p
        <;> ring_nf <;> norm_num
      omega 
    }
    <;> try { trivial }
    <;> try { 
      have h : p ∣ p := by 
        simp
      have : p ∣ a * p ^ 2 := by 
        use a * p
        <;> ring_nf <;> norm_num
      omega 
    }
    <;> try { exfalso <;> try { tauto } <;> try { trivial } <;> try { trivial } <;> try { trivial } }
    all_goals tauto