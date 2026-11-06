import Mathlib

theorem number_theory_108304 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∃ r : ℚ, ∀ n : ℕ, a + n * b = r ^ n) :
    ∃ q : ℚ, b / a = q := by
  rcases h with ⟨r, hr⟩
  have hr0 := hr 0
  have h0 : a = (1 : ℝ) := by
    norm_num at hr0
    linarith
  have hr1 := hr 1
  rw [h0] at hr1
  have hr2 := hr 2
  rw [h0] at hr2
  have eq1 : (1 : ℝ) + b = (r : ℝ) := by
    norm_num at hr1
    linarith
  have eq2 : (1 : ℝ) + 2 * b = (r : ℝ) ^ 2 := by
    norm_num at hr2
    linarith
  have eq5 : b ^ 2 = (0 : ℝ) := by
    have hr_eq : (r : ℝ) = (1 : ℝ) + b := by
      linarith [eq1]
    rw [hr_eq] at eq2
    nlinarith
  have eq6 : b = (0 : ℝ) := by
    nlinarith
  contradiction