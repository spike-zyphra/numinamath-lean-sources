import Mathlib

theorem number_theory_261425 :
    IsLeast {y : ℕ | ∃ x : ℕ, x > 0 ∧ y > 0 ∧ 20 * x + 11 * y = 881} 41 ∧
    IsGreatest {y : ℕ | ∃ x : ℕ, x > 0 ∧ y > 0 ∧ 20 * x + 11 * y = 881} 43 →
    (41 + 43) = 82 := by
  intro h
  rcases h with ⟨h1, h2⟩
  have hx : 41 ∈ {y : ℕ | ∃ x : ℕ, x > 0 ∧ y > 0 ∧ 20 * x + 11 * y = 881} := h1.left
  simp only [Set.mem_setOf_eq] at hx
  rcases hx with ⟨x, hx1, hx2, hx3⟩
  have h4 : 20 * x = 430 := by 
    omega
  exfalso 
  have h5 : (20 * x = 430) := h4
  all_goals
    try { 
      omega 
    }