import Mathlib

theorem algebra_196697 (x a : ℝ) (hx : x = a) (ha : 0 ≤ 3 * x + 1 ∧ 0 ≤ 3 * x + 6 ∧ 0 ≤ 4 * x - 2 ∧ 0 ≤ 4 * x + 3)
    (h : Real.sqrt (3 * x + 1) + Real.sqrt (3 * x + 6) = Real.sqrt (4 * x - 2) + Real.sqrt (4 * x + 3)) :
    a = 3 := by
  rcases ha with ⟨h1, h2, h3, h4⟩
  have h_eq : Real.sqrt (3 * x + 6) - Real.sqrt (4 * x - 2) = Real.sqrt (4 * x + 3) - Real.sqrt (3 * x + 1) := by 
    nlinarith [h]
  have h_eq2 : (Real.sqrt (3 * x + 6) - Real.sqrt (4 * x - 2)) ^ 2 = (Real.sqrt (4 * x + 3) - Real.sqrt (3 * x + 1)) ^ 2 := by
    rw [h_eq]
  have h_eq3 : Real.sqrt (3 * x + 6) ^ 2 + Real.sqrt (4 * x - 2) ^ 2 - 2 * (Real.sqrt (3 * x + 6) * Real.sqrt (4 * x - 2)) =
      Real.sqrt (4 * x + 3) ^ 2 + Real.sqrt (3 * x + 1) ^ 2 - 2 * (Real.sqrt (4 * x + 3) * Real.sqrt (3 * x + 1)) := by
    nlinarith [h_eq2]
  have h_eq4 : Real.sqrt (3 * x + 6) ^ 2 = 3 * x + 6 := Real.sq_sqrt (show 0 ≤ 3 * x + 6 by linarith)
  have h_eq5 : Real.sqrt (4 * x - 2) ^ 2 = 4 * x - 2 := Real.sq_sqrt (show 0 ≤ 4 * x - 2 by linarith)
  have h_eq6 : Real.sqrt (4 * x + 3) ^ 2 = 4 * x + 3 := Real.sq_sqrt (show 0 ≤ 4 * x + 3 by linarith)
  have h_eq7 : Real.sqrt (3 * x + 1) ^ 2 = 3 * x + 1 := Real.sq_sqrt (show 0 ≤ 3 * x + 1 by linarith)
  rw [h_eq4, h_eq5] at h_eq3
  rw [h_eq6, h_eq7] at h_eq3
  have h_eq8 : Real.sqrt (3 * x + 6) * Real.sqrt (4 * x - 2) = Real.sqrt (4 * x + 3) * Real.sqrt (3 * x + 1) := by
    nlinarith
  have h_eq9 : (Real.sqrt (3 * x + 6) * Real.sqrt (4 * x - 2)) ^ 2 = (Real.sqrt (4 * x + 3) * Real.sqrt (3 * x + 1)) ^ 2 := by
    rw [h_eq8]
  have h_eq10 : (Real.sqrt (3 * x + 6) * Real.sqrt (4 * x - 2)) ^ 2 = (3 * x + 6) * (4 * x - 2) := by
    calc
      (Real.sqrt (3 * x + 6) * Real.sqrt (4 * x - 2)) ^ 2 = (Real.sqrt (3 * x + 6) ^ 2) * (Real.sqrt (4 * x - 2) ^ 2) := by 
        ring
      _ = (3 * x + 6) * (4 * x - 2) := by 
        rw [h_eq4, h_eq5]
  have h_eq11 : (Real.sqrt (4 * x + 3) * Real.sqrt (3 * x + 1)) ^ 2 = (4 * x + 3) * (3 * x + 1) := by
    calc
      (Real.sqrt (4 * x + 3) * Real.sqrt (3 * x + 1)) ^ 2 = (Real.sqrt (4 * x + 3) ^ 2) * (Real.sqrt (3 * x + 1) ^ 2) := by 
        ring
      _ = (4 * x + 3) * (3 * x + 1) := by 
        rw [h_eq6, h_eq7]
  rw [h_eq10, h_eq11] at h_eq9
  have h_eq12 : x = 3 := by
    nlinarith
  linarith [hx, h_eq12]