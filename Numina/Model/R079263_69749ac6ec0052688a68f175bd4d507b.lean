import Mathlib

theorem algebra_15899 (lengths heights : Fin 4 → ℝ)
    (h₀ : lengths 0 = 6 ∧ heights 0 = 4)
    (h₁ : lengths 1 = 9 ∧ heights 1 = 3)
    (h₂ : lengths 2 = 6 ∧ heights 2 = 6)
    (h₃ : lengths 3 = 11 ∧ heights 3 = 4) :
    {i | (lengths i / heights i < 1.3 ∨ lengths i / heights i > 2.5)}.encard = 3 := by
  have h0l : lengths 0 = 6 := h₀.1
  have h0h : heights 0 = 4 := h₀.2

  have h1l : lengths 1 = 9 := h₁.1
  have h1h : heights 1 = 3 := h₁.2

  have h2l : lengths 2 = 6 := h₂.1
  have h2h : heights 2 = 6 := h₂.2

  have h3l : lengths 3 = 11 := h₃.1
  have h3h : heights 3 = 4 := h₃.2

  have h4 : {i : Fin 4 | (lengths i / heights i < 1.3 ∨ lengths i / heights i > 2.5)} = {1, 2, 3} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases i <;> simp [h0l, h0h, h1l, h1h, h2l, h2h, h3l, h3h] <;> norm_num
    <;> tauto

  rw [h4]
  rw [Set.encard]
  simp
  all_goals try { tauto }