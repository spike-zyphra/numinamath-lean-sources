import Mathlib

theorem calculus_23142 {a b c : Fin 3 → ℝ}
    (h₀ : crossProduct a b = ![6, -7, 3])
    (h₁ : crossProduct a c = ![4, 7, 2])
    (h₂ : crossProduct b c = ![1, -7, 18]) :
    crossProduct c (3 • a - 2 • b) = ![-10, -35, 30] := by
  have h3 : crossProduct c (3 • a - 2 • b) = 3 • (crossProduct c a) - 2 • (crossProduct c b) := by
    simp [crossProduct]
    <;> ring
  have h4 : crossProduct c a = -(crossProduct a c) := by 
    simp [crossProduct]
    <;> ring_nf
  have h5 : crossProduct c a = ![-4, -7, -2] := by
    rw [h4, h₁]
    all_goals
      simp [Fin.sum_univ_three]
      all_goals
        ring
  -- Derive crossProduct c b from h₂
  have h6 : crossProduct c b = -(crossProduct b c) := by
    simp [crossProduct]
    <;> ring_nf
  have h7 : crossProduct c b = ![-1, 7, -18] := by
    rw [h6, h₂]
    all_goals
      simp [Fin.sum_univ_three]
      all_goals
        ring
  rw [h3]
  rw [h5, h7]
  all_goals 
    simp [crossProduct, Fin.sum_univ_three]
    all_goals 
      ring