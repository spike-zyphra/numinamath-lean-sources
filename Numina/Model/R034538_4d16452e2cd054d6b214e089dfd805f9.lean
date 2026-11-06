import Mathlib

theorem algebra_36949 (n : ℕ) (hn : 0 < n) (x : Fin n → Fin n → ℝ)
    (h : ∀ i j k, x i j + x j k + x k i = 0) :
    ∃ a : Fin n → ℝ, ∀ i j, x i j = a i - a j := by
  
  have h1 : ∀ i : Fin n, x i i = 0 := by
    intro i
    specialize h i i i
    have eq1 : x i i + x i i + x i i = 0 := by
      simpa using h
    have eq2 : x i i = 0 := by
      nlinarith
    exact_mod_cast eq2

  have h2 : ∀ i j : Fin n, x i j = -x j i := by
    intro i j
    have eq1 : x i j + x j i + x i i = 0 := by
      specialize h i j i
      simpa using h
    have eq2 : x i i = 0 := h1 i
    rw [eq2] at eq1
    linarith
  use fun i => x i ⟨0, by linarith⟩
  intro i j 
  have eq1 := h i j ⟨0, by linarith⟩
  have eq6 : x i j + x j ⟨0, by linarith⟩ + x ⟨0, by linarith⟩ i = 0 := by
    simpa using eq1
  have eq4 : x ⟨0, by linarith⟩ i = -x i ⟨0, by linarith⟩ := by
    have eq5 := h2 ⟨0, by linarith⟩ i 
    simpa using eq5 
  linarith [eq4, eq6]