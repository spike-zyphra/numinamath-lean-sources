import Mathlib

theorem fourth_root_value : 
  ∀ (a : ℝ), 
  let P := fun x => (x - 1) * (x - 3) * (x - 5) * (x - a)
  let P' := fun x => (x - 3) * (x - 5) * (x - a) + 
                     (x - 1) * (x - 5) * (x - a) + 
                     (x - 1) * (x - 3) * (x - a) + 
                     (x - 1) * (x - 3) * (x - 5)
  (P 1 = 0 ∧ P 3 = 0 ∧ P 5 = 0 ∧ P' 7 = 0) → a = 89/11 := by 
  intro a P P'
  rintro ⟨h1, h3, h5, h7⟩
  simp [P] at h1 h3 h5 
  have eq1 : P' 7 = (7 - 3) * (7 - 5) * (7 - a) + (7 - 1) * (7 - 5) * (7 - a) + 
          (7 - 1) * (7 - 3) * (7 - a) + (7 - 1) * (7 - 3) * (7 - 5) := by
    simp [P']
  rw [eq1] at h7
  have eq0 : (7 - 3) * (7 - 5) * (7 - a) + (7 - 1) * (7 - 5) * (7 - a) + 
          (7 - 1) * (7 - 3) * (7 - a) + (7 - 1) * (7 - 3) * (7 - 5) = 44 * (7 - a) + 48 := by 
    ring
  have eq2 : 44 * (7 - a) + 48 = 0 := by
    linarith [h7, eq0]
  have ha : a = 89 / 11 := by 
    linarith 
  assumption