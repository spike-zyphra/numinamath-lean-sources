import Mathlib

theorem number_theory_293772 (a b : Fin 2019 → ℝ)
    (ha : ∀ i j, a i = a j → i = j)
    (hb : ∀ i j, b i = b j → i = j)
    (h : ∀ i, ∃ x y, x ≠ y ∧ a i + b i = x + y ∧ ∃ q : ℚ, x + y = q) :
    {i | ¬(∃ x : ℝ, x = a i ∨ x = b i)}.encard ≤ 2016 := by
  have h1 : ∀ i : Fin 2019, (∃ x : ℝ, x = a i ∨ x = b i) := by
    intro i 
    refine' ⟨a i, Or.inl rfl⟩ 
  have h2 : ∀ i : Fin 2019, ¬(¬(∃ x : ℝ, x = a i ∨ x = b i)) := by
    intro i 
    have h3 := h1 i 
    tauto 
  have h3 : {i : Fin 2019 | ¬(∃ x : ℝ, x = a i ∨ x = b i)} = ∅ := by
    ext i 
    simp [h2] 
  rw [h3] 
  simp