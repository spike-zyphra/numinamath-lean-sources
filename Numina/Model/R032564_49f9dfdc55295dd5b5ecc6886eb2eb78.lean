import Mathlib

theorem algebra_282230 :
  {(x, y, z) : ℕ × ℕ × ℕ | 
    x + y + z = 560 ∧ 
    70*x + 64*y + 50*z = 60*(x + y + z) ∧
    ∃ q : ℕ, q ≤ 40 ∧ x = 7*q ∧ y = 400 - 10*q ∧ z = 160 + 3*q} =
  { (x, y, z) : ℕ × ℕ × ℕ | ∃ q : ℕ, q ≤ 40 ∧ x = 7*q ∧ y = 400 - 10*q ∧ z = 160 + 3*q} := by 
  ext ⟨x, y, z⟩
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor 
  · -- Assume ⟨x, y, z⟩ is in left side, so ⟨x, y, z⟩ must be in right side
    rintro ⟨h1, h2, ⟨q, hq, hx1, hy1, hz1⟩⟩ 
    exact ⟨q, hq, hx1, hy1, hz1⟩
  · -- Assume ⟨x, y, z⟩ is in right side, so ⟨x, y, z⟩ must be in left side 
    rintro ⟨q, hq, hx1, hy1, hz1⟩ 
    have h1 : x + y + z = 560 := by 
      omega 
    have h2 : 70*x + 64*y + 50*z = 60*(x + y + z) := by 
      omega 
    exact ⟨h1, h2, ⟨q, hq, hx1, hy1, hz1⟩⟩