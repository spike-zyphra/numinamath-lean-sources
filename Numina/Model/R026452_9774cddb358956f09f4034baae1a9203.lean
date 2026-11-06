import Mathlib

theorem algebra_160334 (x1 x2 m n : ℤ) (y1 y2 : ℝ) (hmn : ¬m ∣ n)
    (hxy : x2 = x1 + m ∧ y2 = y1 + n) :
    ¬∃ b c : ℤ, (x1 ^ 2 + b * x1 + c = y1 ∧ x2 ^ 2 + b * x2 + c = y2) := by 
  intro h 
  rcases h with ⟨b, c, heq1, heq2⟩
  rcases hxy with ⟨hx2, hy2⟩
  have eq1 : (x1 : ℝ) ^ 2 + (b : ℝ) * (x1 : ℝ) + (c : ℝ) = (y1 : ℝ) := by
    exact_mod_cast heq1
  have eq2 : (x2 : ℝ) ^ 2 + (b : ℝ) * (x2 : ℝ) + (c : ℝ) = (y2 : ℝ) := by
    exact_mod_cast heq2
  have eq3 : ((x2 : ℝ) - (x1 : ℝ)) * ((x2 : ℝ) + (x1 : ℝ) + (b : ℝ)) = (y2 - y1) := by
    nlinarith
  have eq4 : (x2 : ℝ) - (x1 : ℝ) = (m : ℝ) := by
    have h1 : (x2 : ℝ) = (x1 : ℝ) + (m : ℝ) := by
      exact_mod_cast hx2
    nlinarith
  have eq5 : (y2 - y1) = (n : ℝ) := by
    have h2 : (y2 : ℝ) = (y1 : ℝ) + (n : ℝ) := by
      exact_mod_cast hy2
    nlinarith
  rw [eq4, eq5] at eq3
  have eq6 : (m : ℝ) * ((x1 + x2 + b) : ℝ) = (n : ℝ) := by
    ring_nf at eq3 ⊢
    linarith
  have eq7 : (m : ℤ) * ((x1 + x2 + b) : ℤ) = (n : ℤ) := by
    exact_mod_cast eq6
  have h1 : m ∣ n := by 
    use (x1 + x2 + b)
    all_goals linarith 
  contradiction