import Mathlib

theorem algebra_17256 (a : ℕ → ℝ) (hageom : ∃ r, ∀ n, a (n + 1) = r * a n)
    (hapos : ∀ n, 0 < a n) (ha5 : a 4 = 11) (ha11 : a 10 = 5) :
    a 7 = √55 := by
  rcases hageom with ⟨r, hr⟩
  have ha7 : a 7 = a 4 * r ^ 3 := by
    have h1 : a 5 = r * a 4 := by apply hr 4
    have h2 : a 6 = r * a 5 := by apply hr 5
    have h3 : a 7 = r * a 6 := by apply hr 6
    rw [h1] at h2
    rw [h2] at h3
    linarith [h3, ha5]
  have ha11_eq : a 10 = a 7 * r ^ 3 := by
    have h1 : a 8 = r * a 7 := by apply hr 7
    have h2 : a 9 = r * a 8 := by apply hr 8
    have h3 : a 10 = r * a 9 := by apply hr 9
    rw [h1] at h2
    rw [h2] at h3
    linarith [h3]
  have eq1 : a 7 ^ 2 = 55 := by
    have eq2 : a 7 = a 4 * r ^ 3 := ha7
    have eq3 : a 10 = a 7 * r ^ 3 := ha11_eq
    have eq4 : a 7 = 11 * r ^ 3 := by 
      rw [ha5] at eq2
      linarith
    have eq5 : (5 : ℝ) = a 7 * r ^ 3 := by 
      linarith [eq3, ha11]
    have eq6 : a 7 ^ 2 = 55 := by
      have eq7 : 5 = 11 * r ^ 6 := by 
        rw [show a 7 = 11 * r ^ 3 by linarith [eq4]] at eq5
        nlinarith [sq_nonneg (a 7), sq_nonneg (r ^ 3), hapos 4, hapos 7, hapos 10]
      have eq8 : r ^ 6 = (5 / 11 : ℝ) := by 
        linarith [eq7]
      have eq15 : a 7 ^ 2 = 121 * r ^ 6 := by
        calc
          a 7 ^ 2 = (11 * r ^ 3) ^ 2 := by 
            rw [eq4]
          _ = 121 * (r ^ 3) ^ 2 := by 
            ring
          _ = 121 * r ^ 6 := by 
            have heq3 : (r ^ 3) ^ 2 = r ^ 6 := by ring_nf
            rw [heq3]
      have heq4 : r ^ 6 = (5 / 11 : ℝ) := eq8
      nlinarith [eq15, heq4]
    exact_mod_cast eq6
  have h7_pos : 0 < a 7 := hapos 7
  have h8 : a 7 = Real.sqrt (55 : ℝ) := by
    have h9 : Real.sqrt (a 7 ^ 2) = Real.sqrt (55 : ℝ) := by
      rw [eq1]
    have h10 : Real.sqrt (a 7 ^ 2) = a 7 := by
      rw [Real.sqrt_sq (by linarith [h7_pos])]
    linarith [h9, h10]
  exact_mod_cast h8