import Mathlib

theorem algebra_234818 {a b c : ℚ} (ha : a > 0) (h : ∀ x : ℤ, ∃ n : ℤ, a * x ^ 2 + b * x + c = n) :
    a ≥ 1 / 2 := by
  have h0 := h 0
  rcases h0 with ⟨n0, hn0⟩
  have h1 : c = (n0 : ℚ) := by 
    norm_num at hn0 ⊢
    linarith
  have h2 := h 1
  rcases h2 with ⟨n1, hn1⟩
  have eq1 : a + b + c = (n1 : ℚ) := by
    norm_num at hn1 ⊢
    linarith
  have h3 := h 2
  rcases h3 with ⟨n2, hn2⟩
  have eq2 : 4 * a + 2 * b + c = (n2 : ℚ) := by
    norm_num at hn2 ⊢
    linarith
  have eq3 : a + b = (n1 - n0 : ℚ) := by
    linarith [h1, eq1]
  have eq4 : 4 * a + 2 * b = (n2 - n0 : ℚ) := by
    linarith [h1, eq2]
  have eq6 : 2 * a = (n2 - 2 * n1 + n0 : ℚ) := by 
    nlinarith [eq3, eq4]
  have eq7 : 2 * a ≥ (1 : ℚ) := by
    have eq8 : 2 * a = (n2 - 2 * n1 + n0 : ℚ) := eq6
    have eq9 : (n2 - 2 * n1 + n0 : ℚ) = (n2 - 2 * n1 + n0 : ℤ) := by
      simp
    rw [eq9] at eq8
    have eq10 : (n2 - 2 * n1 + n0 : ℤ) > 0 := by
      by_contra h'
      push_neg at h'
      have h11 : (n2 - 2 * n1 + n0 : ℤ) ≤ 0 := by omega
      have eq11 : (n2 - 2 * n1 + n0 : ℚ) ≤ (0 : ℚ) := by
        exact_mod_cast h11
      have eq12 : 2 * a ≤ (0 : ℚ) := by
        nlinarith [eq8, eq11]
      nlinarith
    have eq13 : (n2 - 2 * n1 + n0 : ℤ) ≥ 1 := by 
      omega
    have eq14 : (n2 - 2 * n1 + n0 : ℚ) ≥ (1 : ℚ) := by 
      exact_mod_cast eq13
    nlinarith [eq8, eq14]
  linarith
  all_goals linarith