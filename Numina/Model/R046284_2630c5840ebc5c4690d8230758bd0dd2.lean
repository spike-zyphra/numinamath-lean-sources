import Mathlib

theorem algebra_119600 (a : Fin 5 → Fin 5 → ℝ)
    (h₀ : ∀ i, ∃ d, ∀ j, a i j = a i 0 + d * j)
    (h₁ : ∀ j, ∃ d, ∀ i, a i j = a 0 j + d * i)
    (h₂ : a 0 0 = 1) (h₃ : a 0 4 = 25) (h₄ : a 4 0 = 81) (h₅ : a 4 4 = 17) :
    a 2 2 = 31 := by
  rcases h₀ 0 with ⟨d0, hd0⟩
  have eq1 : a 0 4 = a 0 0 + d0 * 4 := by
    simpa using hd0 4
  rw [h₂] at eq1
  rw [h₃] at eq1
  have d0_eq : d0 = 6 := by
    linarith

  rcases h₁ 0 with ⟨e0, he0⟩
  have eq2 : a 4 0 = a 0 0 + e0 * 4 := by
    simpa using he0 4
  rw [h₂] at eq2
  rw [h₄] at eq2
  have e0_eq : e0 = 20 := by
    linarith

  rcases h₀ 4 with ⟨d4, hd4⟩
  have eq3 : a 4 4 = a 4 0 + d4 * 4 := by
    simpa using hd4 4
  rw [h₄] at eq3
  rw [h₅] at eq3
  have d4_eq : d4 = -16 := by
    linarith

  rcases h₁ 4 with ⟨e4, he4⟩
  have eq4 : a 4 4 = a 0 4 + e4 * 4 := by
    simpa using he4 4
  rw [h₃] at eq4
  rw [h₅] at eq4
  have e4_eq : e4 = -2 := by
    linarith

  have a02_eq : a 0 2 = 13 := by
    have eq5 : a 0 2 = a 0 0 + d0 * 2 := by
      simpa using hd0 2
    rw [h₂, d0_eq] at eq5
    linarith

  have a42_eq : a 4 2 = 49 := by
    have eq6 : a 4 2 = a 4 0 + d4 * 2 := by
      simpa using hd4 2
    rw [h₄, d4_eq] at eq6
    linarith

  rcases h₁ 2 with ⟨e2, he2⟩
  have eq7 : a 4 2 = a 0 2 + e2 * 4 := by
    simpa using he2 4
  rw [a42_eq, a02_eq] at eq7
  have e2_eq : e2 = 9 := by
    linarith

  have eq8 : a 2 2 = a 0 2 + e2 * 2 := by
    simpa using he2 2
  rw [a02_eq, e2_eq] at eq8
  linarith