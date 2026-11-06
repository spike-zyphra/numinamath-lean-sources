import Mathlib

theorem algebra_172504 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => x^2 + a * x + b)
    (h1 : f 2 + f 4 = 2 * 2023 * 3) :
    f 3 = 6068 := by
  rcases hf with ⟨a, b, hf_eq⟩
  have eq1 : f 2 = 2 ^ 2 + a * 2 + b := by
    rw [hf_eq]
  have eq2 : f 4 = 4 ^ 2 + a * 4 + b := by
    rw [hf_eq]
  have eq3 : f 3 = 3 ^ 2 + a * 3 + b := by
    rw [hf_eq]
  rw [eq1, eq2] at h1
  rw [eq3]
  have h3 : 20 + 6 * a + 2 * b = 12138 := by
    nlinarith
  have h4 : 3 * a + b = 6059 := by
    linarith [h3]
  have hb : b = 6059 - 3 * a := by
    linarith [h4]
  rw [hb]
  ring_nf