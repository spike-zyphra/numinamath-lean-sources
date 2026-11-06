import Mathlib

theorem algebra_173898 {r s t : ℝ} (P : ℝ → ℝ) (hP : P = fun x => x^3 + x^2 - r^2 * x - 2020)
    (hroots : {r, s, t} = P⁻¹' {0}) : P 1 = -4038 := by
  have hPr : P r = 0 := by
    have h1 : r ∈ (P⁻¹' {0} : Set ℝ) := by
      have h2 : r ∈ ({r, s, t} : Set ℝ) := by
        simp
      rw [show ({r, s, t} : Set ℝ) = (P⁻¹' {0} : Set ℝ) by rw [hroots] ] at h2
      exact_mod_cast h2
    simpa using h1
  -- Now compute r^2.
  -- P(r) = r^3 + r^2 - r^2 * r - 2020 = r^2 - 2020 = 0. Hence r^2 = 2020
  have hr2 : r ^ 2 = 2020 := by
    rw [hP] at hPr
    simp at hPr 
    linarith
  -- Now compute P 1
  have h3 : P 1 = -4038 := by
    rw [hP]
    simp at *
    rw [hr2]
    norm_num
  exact h3