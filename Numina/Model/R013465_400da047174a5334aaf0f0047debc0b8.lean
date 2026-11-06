import Mathlib

theorem algebra_323897 (a b c : ℝ) (ha : a > 0) (h1 : a * 4^2 + b * 4 + c = -6) (h2 : a * (-2)^2 + b * (-2) + c = 0)
    (A B C : ℝ × ℝ) (hA : A.1 = -c / a) (hB : B.1 = -b / (2 * a)) (hC : C.1 = 0 ∧ C.2 = c)
    (hS : S = (1 / 2) * (B.1 - A.1) * C.2) :
    S ≥ 10 + 4 * Real.sqrt 6 := by
  rcases hC with ⟨hC1, hC2⟩
  have eq1 : 16 * a + 4 * b + c = -6 := by
    nlinarith
  have eq2 : 4 * a - 2 * b + c = 0 := by
    nlinarith
  have eq3 : 12 * a + 6 * b = -6 := by
    nlinarith [eq1, eq2]
  have eq4 : 2 * a + b = -1 := by
    nlinarith
  have eq5 : c = -8 * a - 2 := by
    have eq6 : c = -4 * a + 2 * b := by
      nlinarith [eq2]
    have eq7 : b = -1 - 2 * a := by
      nlinarith [eq4]
    rw [eq7] at eq6
    linarith
  have hS' : S = (c * (-b + 2 * c)) / (4 * a) := by
    have h10 : S = (1 / 2) * (B.1 - A.1) * C.2 := by
      linarith [hS]
    rw [h10, hC2, hA, hB]
    field_simp
    ring
  rw [hS']
  have h3 : c * (-b + 2 * c) = 112 * a ^ 2 + 52 * a + 6 := by
    have eq2' : c = -8 * a - 2 := by linarith [eq5]
    have eq3' : b = -1 - 2 * a := by linarith [eq4]
    rw [eq2', eq3']
    nlinarith
  rw [h3]
  have h5 : (112 * a ^ 2 + 52 * a + 6) / (4 * a) ≥ 10 + 4 * Real.sqrt 6 := by
    have ha1 : a > 0 := ha
    have h6 : (112 * a ^ 2 + 52 * a + 6) ≥ 4 * a * (10 + 4 * Real.sqrt 6) := by
      nlinarith [sq_nonneg (a - Real.sqrt 6 / 6), sq_nonneg (a + Real.sqrt 6 / 6), Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by linarith)]
    have h7 : (112 * a ^ 2 + 52 * a + 6) / (4 * a) ≥ 10 + 4 * Real.sqrt 6 := by
      have ha1 : a > 0 := ha
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    exact h7
  exact h5