import Mathlib

theorem algebra_16940 {p : ℝ → ℝ} (hp : ∃ a b c, p = fun x => a * x ^ 2 + b * x + c)
    (h1 : p (-7) = 0) (h2 : p 4 = 0) (h3 : p 5 = -36) :
    p = fun x => -3 * x ^ 2 - 9 * x + 84 := by 
  rcases hp with ⟨a, b, c, hp⟩
  have eq1 : a * (-7) ^ 2 + b * (-7) + c = 0 := by
    rw [hp] at h1
    exact h1
  have eq2 : a * 4 ^ 2 + b * 4 + c = 0 := by
    rw [hp] at h2
    exact h2
  have eq3 : a * 5 ^ 2 + b * 5 + c = -36 := by
    rw [hp] at h3
    exact h3
  have eq4 : b = 3 * a := by 
    linarith [eq1, eq2]
  have eq5 : 9 * a + b = -36 := by
    linarith
  have eq6 : a = -3 := by 
    rw [eq4] at eq5
    linarith
  have eq7 : b = -9 := by 
    rw [eq6] at eq4
    linarith
  have eq8 : c = 84 := by
    rw [eq6, eq7] at eq2
    linarith 
  ext x
  simp [hp, eq6, eq7, eq8]
  <;> ring_nf
  <;> norm_num
  <;> tauto