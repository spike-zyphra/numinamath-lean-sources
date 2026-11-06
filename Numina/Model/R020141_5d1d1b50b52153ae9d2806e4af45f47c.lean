import Mathlib

theorem algebra_323983 {f g : ℝ → ℝ} (hf : f = fun x => (2 * x + 3) / (x - 1))
    (hg : ∀ x, ∃ y, g x = y ∧ f y = x + 1) :
    g 3 = 7 / 2 := by
  have h1 : ∃ y, g 3 = y ∧ f y = 3 + 1 := hg 3
  rcases h1 with ⟨y, h11, h12⟩
  have eq1 : f y = (2 * y + 3) / (y - 1) := by
    rw [hf]
  have eq2 : f y = 4 := by
    linarith
  rw [eq1] at eq2
  have eq3 : y - 1 ≠ 0 := by
    by_contra h
    have h2 : y = 1 := by linarith
    rw [h2] at eq2
    norm_num at eq2
    all_goals tauto
  have eq4 : 2 * y + 3 = 4 * (y - 1) := by
    have eq5 : 2 * y + 3 = 4 * (y - 1) := by
      field_simp [eq3] at eq2
      linarith
    linarith
  have eq5 : 2 * y = 7 := by
    linarith
  have eq6 : y = 7 / 2 := by
    linarith
  rw [h11]
  linarith