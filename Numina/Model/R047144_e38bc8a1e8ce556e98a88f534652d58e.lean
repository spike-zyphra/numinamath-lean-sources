import Mathlib

theorem algebra_123753 : ¬∃ f : ℝ → ℝ, Function.Surjective f ∧ ∀ x, f (f x) = (x - 1) * f x + 2 := by
  rintro ⟨f, hf1, hf2⟩
  have h1 : ∀ x, f (f x) = (x - 1) * f x + 2 := hf2
  have h2 : ∀ y, ∃ x, f x = y := hf1 
  have h3 : f 0 = 2 := by
    have h4 : ∃ b, f b = 0 := h2 0
    rcases h4 with ⟨b, hb⟩
    have eq1 := h1 b
    simp [hb] at eq1 
    linarith
  have h4 : ∃ a, f a = 1 := h2 1
  rcases h4 with ⟨a, ha⟩
  have eq2 := h1 a
  simp [ha] at eq2
  have eq3 : f 1 = a + 1 := by linarith
  have eq4 : f (a + 1) = 2 := by 
    have eq5 := h1 1
    simp [eq3] at eq5 
    linarith
  have eq6 : f 2 = 2 * a + 2 := by
    have eq7 := h1 (a + 1)
    simp [eq4] at eq7 
    linarith
  have eq8 : f 2 = 0 := by
    have eq9 := h1 0
    simp [h3] at eq9 
    linarith
  have ha1 : a = -1 := by linarith [eq6, eq8]
  have eq3 : f 1 = 0 := by 
    rw [eq3]
    linarith [ha1]
  have eq10 : ∃ d, f d = a := h2 a
  rcases eq10 with ⟨d, hd⟩
  have eq11 : f d = a := hd 
  have eq12 : f (f d) = (d - 1) * f d + 2 := h1 d
  rw [eq11] at eq12 
  have eq15 : d = 2 := by 
    have eq13a : f a = 1 := ha
    rw [eq13a] at eq12
    rw [show a = -1 by linarith [ha1] ] at eq12
    nlinarith 
  have eq19 : f 2 = -1 := by
    have eq11a : f 2 = a := by
      rw [show d = 2 by linarith [eq15]] at eq11
      linarith
    rw [eq11a]
    linarith [ha1]
  linarith [eq19, eq8]