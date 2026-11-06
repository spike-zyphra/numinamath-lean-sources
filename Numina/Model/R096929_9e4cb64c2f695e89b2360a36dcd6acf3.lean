import Mathlib

theorem algebra_246520 (x y z t : ℤ) (h₀ : x ≠ y) (h₁ : x ≠ z) (h₂ : x ≠ t)
    (h₃ : y ≠ z) (h₄ : y ≠ t) (h₅ : z ≠ t) (h₆ : x * y - x * z + y * t = 182)
    (h₇ : x = 12 ∨ x = 14 ∨ x = 37 ∨ x = 65) (h₈ : y = 12 ∨ y = 14 ∨ y = 37 ∨ y = 65)
    (h₉ : z = 12 ∨ z = 14 ∨ z = 37 ∨ z = 65) (h₁₀ : t = 12 ∨ t = 14 ∨ t = 37 ∨ t = 65) :
    x = 12 ∧ y = 37 ∧ z = 65 ∧ t = 14 := by
  rcases h₇ with hx | hx | hx | hx <;> rcases h₈ with hy | hy | hy | hy <;> 
    rcases h₉ with hz | hz | hz | hz <;> rcases h₁₀ with ht | ht | ht | ht 
      <;> simp [hx, hy, hz, ht] at h₆ ⊢ 
      <;> try { tauto }
      <;> try { linarith }
      <;> try { omega }
      <;> try { contradiction }
      <;> try { omega }