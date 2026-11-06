import Mathlib

theorem algebra_636 {m s : ℕ} (h0 : m + s > 0) (h1 : (m + s) * 5 = (2 * m + 4 * s) * 2) :
    m / s = (3 : ℝ) := by
  have h2 : m = 3 * s := by 
    omega 
  have h3 : s > 0 := by
    by_cases h : s > 0 
    · exact h 
    · -- Assume not, s <= 0, since s is natural, s = 0
      have hs : s = 0 := by 
        omega 
      have hm : m = 0 := by 
        simp [hs] at h2 
        omega 
      have h4 : m + s = 0 := by 
        simp [hm, hs] 
      omega 
  have h4 : (m : ℝ) = 3 * (s : ℝ) := by
    exact_mod_cast h2 
  have h5 : (s : ℝ) > (0 : ℝ) := by 
    exact_mod_cast h3 
  have h6 : (m : ℝ) / (s : ℝ) = (3 : ℝ) := by
    rw [show (m : ℝ) = 3 * (s : ℝ) by linarith [h4]]
    have h8 : (s : ℝ) ≠ (0 : ℝ) := by 
      linarith 
    field_simp [h8] 
  exact_mod_cast h6