import Mathlib

theorem algebra_285533 {P Q : ℤ} (hP : P = 1) (hQ : Q = 2) :
    ¬∃ n : ℤ, (P / Q : ℝ) = n := by 
  rw [hP, hQ]
  rintro ⟨n, hn⟩
  have h1 : (1 / 2 : ℝ) = (n : ℝ) := by
    simpa using hn
  have h2 : (n : ℝ) = (1 / 2 : ℝ) := by 
    linarith
  have h5 : (2 * (n : ℝ) : ℝ) = (1 : ℝ) := by 
    linarith
  have h6 : (2 * n : ℤ) = (1 : ℤ) := by 
    exact_mod_cast h5
  omega