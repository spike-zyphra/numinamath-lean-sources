import Mathlib

theorem algebra_114921 {x y z : ℝ} (h1 : ∃ q : ℚ, x + y * z = q)
    (h2 : ∃ q : ℚ, y + z * x = q) (h3 : ∃ q : ℚ, z + x * y = q)
    (h4 : x ^ 2 + y ^ 2 = 1) : ∃ q : ℚ, x * y * z ^ 2 = q := by
  rcases h1 with ⟨q1, h1⟩
  rcases h2 with ⟨q2, h2⟩
  rcases h3 with ⟨q3, h3⟩

  have h_eq1 : (q1 : ℝ) * (q2 : ℝ) = x * y + z * (x ^ 2 + y ^ 2) + x * y * z ^ 2 := by
    calc
      (q1 : ℝ) * (q2 : ℝ) = (x + y * z) * (y + z * x) := by rw [h1, h2]
      _ = x * y + x ^ 2 * z + y ^ 2 * z + x * y * z ^ 2 := by ring_nf
      _ = x * y + z * (x ^ 2 + y ^ 2) + x * y * z ^ 2 := by ring_nf
      _ = x * y + z * (x ^ 2 + y ^ 2) + x * y * z ^ 2 := by ring_nf

  have h_eq2 : (q1 : ℝ) * (q2 : ℝ) = x * y + z + x * y * z ^ 2 := by
    rw [h_eq1]
    have h5 : x ^ 2 + y ^ 2 = 1 := h4
    rw [h5]
    all_goals nlinarith
    all_goals ring_nf
    all_goals nlinarith

  have h_eq3 : z = (q3 : ℝ) - x * y := by
    have hz : z + x * y = (q3 : ℝ) := by 
      linarith
    linarith

  have h_eq4 : x * y * z ^ 2 = (q1 : ℝ) * (q2 : ℝ) - (q3 : ℝ) := by
    have eq1 : (q1 : ℝ) * (q2 : ℝ) = x * y + z + x * y * z ^ 2 := by linarith [h_eq2]
    rw [h_eq3] at eq1
    have eq2 : x * y * z ^ 2 = (q1 : ℝ) * (q2 : ℝ) - (q3 : ℝ) := by
      nlinarith
      all_goals nlinarith
    linarith [eq2]

  refine' ⟨q1 * q2 - q3, by
    exact_mod_cast h_eq4
  ⟩