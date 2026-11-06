import Mathlib

theorem algebra_1575 {n m : ℕ} (h1 : n < 100) (h2 : n > 9)
    (h₃ : m > 99) (h₄ : m < 1000) (h₅ : (n : ℝ) / 100 * (m : ℝ) = 777) : n = 84 := by 
  have h6 : (n : ℝ) * (m : ℝ) = 77700 := by
    ring_nf at h₅
    nlinarith
  have h7 : n * m = 77700 := by
    have h8 : (n * m : ℝ) = (77700 : ℝ) := by
      nlinarith
    have h9 : (n * m : ℝ) = (n * m : ℕ) := by simp
    have h10 : (77700 : ℝ) = (77700 : ℕ) := by simp
    rw [h9, h10] at h8
    exact_mod_cast h8
  interval_cases n <;> omega