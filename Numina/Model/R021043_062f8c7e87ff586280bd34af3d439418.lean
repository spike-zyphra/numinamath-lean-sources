import Mathlib

theorem algebra_148036 (a : ℕ → ℤ) (h : ∀ n, a (n + 1) - a n = 5) (ha : a 1 = 37) :
    ¬(500 ∈ {x | ∃ n, x = a n}) ∧ ¬(1000 ∈ {x | ∃ n, x = a n}) ∧
    ¬(1500 ∈ {x | ∃ n, x = a n}) ∧ ¬(2000 ∈ {x | ∃ n, x = a n}) := by
  have h1 : ∀ n, a (n + 1) = a n + 5 := by
    intro n 
    specialize h n
    linarith

  have h2 : ∀ n : ℕ, a n = 32 + 5 * (n : ℤ) := by 
    intro n
    induction n with 
    | zero =>
      have h0 : a 0 = 32 := by
        have eq1 := h 0
        simp at eq1 
        linarith [ha]
      simp [h0]
      <;> omega 
    | succ n ih =>
      have eq1 := h1 n
      simp [eq1, ih] at *
      <;> ring_nf
      <;> omega 
  have h3 : ¬(500 ∈ {x | ∃ n, x = a n}) := by
    simp only [Set.mem_setOf_eq]
    rintro ⟨n, hn⟩
    rw [h2 n] at hn
    omega 
  have h4 : ¬(1000 ∈ {x | ∃ n, x = a n}) := by
    simp only [Set.mem_setOf_eq]
    rintro ⟨n, hn⟩
    rw [h2 n] at hn
    omega 
  have h5 : ¬(1500 ∈ {x | ∃ n, x = a n}) := by
    simp only [Set.mem_setOf_eq]
    rintro ⟨n, hn⟩
    rw [h2 n] at hn
    omega 
  have h6 : ¬(2000 ∈ {x | ∃ n, x = a n}) := by
    simp only [Set.mem_setOf_eq]
    rintro ⟨n, hn⟩
    rw [h2 n] at hn
    omega 
  exact ⟨h3, h4, h5, h6⟩