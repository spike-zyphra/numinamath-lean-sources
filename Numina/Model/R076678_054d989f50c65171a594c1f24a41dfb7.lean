import Mathlib

theorem algebra_242316 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (hA : f (1 / 2) = 3 / 4) (hB : f (-1) = 3) (hC : f 2 = 3) :
    f = fun x => x ^ 2 - x + 1 := by
  rcases hf with ⟨a, b, c, h_def⟩
  have eq1 : a * (1/2) ^ 2 + b * (1/2) + c = 3/4 := by
    rw [h_def] at hA
    simpa using hA
  have eq2 : a * (-1) ^ 2 + b * (-1) + c = 3 := by
    rw [h_def] at hB
    simpa using hB
  have eq3 : a * 2 ^ 2 + b * 2 + c = 3 := by
    rw [h_def] at hC
    simpa using hC
  have eq4 : a + b = 0 := by
    nlinarith [eq2, eq3]
  have eq5 : c = 3 + 2 * b := by
    linarith [eq2, eq4]
  have eq6 : b = -1 := by
    rw [eq5, show a = -b by linarith [eq4]] at eq1
    nlinarith
  have eq7 : a = 1 := by
    linarith [eq4, eq6]
  have eq8 : c = 1 := by
    linarith [eq5, eq6]
  ext x
  simp [h_def, eq7, eq6, eq8]
  <;> ring