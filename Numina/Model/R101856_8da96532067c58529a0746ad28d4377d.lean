import Mathlib

theorem algebra_13643 {f : ℝ → ℝ} (hf : ∃ p q r s : ℝ, f = fun x => p*x^3 + q*x^2 + r*x + s)
    (h1 : f 1 = 1) (h2 : f 2 = 2) (h3 : f 3 = 4) (h4 : f 4 = 6) :
    f 5 = 7 := by
  rcases hf with ⟨p, q, r, s, hf_eq⟩
  have eq1 : p * (1:ℝ)^3 + q * (1:ℝ)^2 + r * (1:ℝ) + s = 1 := by
    rw [hf_eq] at h1
    simpa using h1
  have eq2 : p * (2:ℝ)^3 + q * (2:ℝ)^2 + r * (2:ℝ) + s = 2 := by
    rw [hf_eq] at h2
    simpa using h2
  have eq3 : p * (3:ℝ)^3 + q * (3:ℝ)^2 + r * (3:ℝ) + s = 4 := by
    rw [hf_eq] at h3
    simpa using h3
  have eq4 : p * (4:ℝ)^3 + q * (4:ℝ)^2 + r * (4:ℝ) + s = 6 := by
    rw [hf_eq] at h4
    simpa using h4
  have eq5 : p * (5:ℝ)^3 + q * (5:ℝ)^2 + r * (5:ℝ) + s = 7 := by
    linarith [eq1, eq2, eq3, eq4]
  rw [hf_eq]
  simp only [eq5]
  <;> linarith