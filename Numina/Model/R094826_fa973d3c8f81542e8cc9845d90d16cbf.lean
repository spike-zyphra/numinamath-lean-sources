import Mathlib

theorem algebra_110438 {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : (0.4 * m : ℝ) = (0.8 * n : ℝ)) :
    (n / (m + n : ℝ)) * 100 = 33 + 1 / 3 := by
  have h1 : (m : ℝ) = 2 * (n : ℝ) := by
    have eq1 : (0.4 * (m : ℝ)) = (0.8 * (n : ℝ)) := by
      simpa using h
    ring_nf at eq1
    linarith
  have h2 : (m + n : ℝ) = 3 * (n : ℝ) := by
    have h1' : (m : ℝ) = 2 * (n : ℝ) := by linarith
    linarith
  have h3 : (n : ℝ) ≠ 0 := by 
    exact_mod_cast hn
  have eq3 : (n / ((m + n : ℝ)) ) * 100 = (1/3) * 100 := by
    have h1' : (m + n : ℝ) = 3 * (n : ℝ) := by linarith
    have eq4 : (n : ℝ) / ((m + n : ℝ)) = (1 / 3 : ℝ) := by
      rw [h1']
      have h2 : (n : ℝ) ≠ 0 := by 
        exact_mod_cast hn
      field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn]
      <;> linarith
    rw [eq4]
    <;> norm_num
  linarith [eq3]