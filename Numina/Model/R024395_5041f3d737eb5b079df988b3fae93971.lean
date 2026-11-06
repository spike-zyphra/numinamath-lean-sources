import Mathlib

theorem algebra_268615 (k l m : ℝ) (hm : m ≠ 0) (f g : ℝ → ℝ)
    (hf : f = fun x => k + m / (x - l)) (hg : g = fun x => l + m / (x - k))
    (h1 : f 1 = 4) (h2 : g 2 = 3) (h3 : f 2 = 4) :
    f (k + l + m) = 1 := by
  simp [hf] at h1 h3
  have eq1 : k + m / (1 - l) = 4 := by
    simpa using h1
  have eq2 : k + m / (2 - l) = 4 := by
    simpa using h3
  have eq3 : m / (1 - l) = m / (2 - l) := by
    have eq4 : k + m / (1 - l) = k + m / (2 - l) := by
      linarith [eq1, eq2]
    have eq5 : m / (1 - l) = m / (2 - l) := by
      linarith [eq4]
    linarith [eq5]
  have eq6 : (1 - l) ≠ 0 := by
    by_contra h
    have hl1 : l = 1 := by linarith
    rw [hl1] at eq1 eq2
    field_simp at eq1 eq2
    all_goals
      exfalso
      apply hm
      linarith
  have eq7 : (2 - l) ≠ 0 := by
    by_contra h
    have hl2 : l = 2 := by linarith
    rw [hl2] at eq1 eq2
    field_simp at eq1 eq2
    all_goals
      exfalso
      apply hm
      linarith
  have eq8 : m / (1 - l) - m / (2 - l) = 0 := by
    linarith [eq3]
  have eq9 : m * (2 - l) - m * (1 - l) = 0 := by
    field_simp [eq6, eq7] at eq8 ⊢
    <;> nlinarith [eq8]
  have eq10 : m = 0 := by
    linarith [eq9]
  exfalso
  apply hm
  exact eq10