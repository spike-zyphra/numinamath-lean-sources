import Mathlib

theorem algebra_3501 {b c : ℝ}
  (h : ∃x, x^2+b*x+c = 0 ∧ b*x^2+c*x+1 = 0) :
  b+c+1=0 ∨ b^2+c^2+1=b*c+b+c:= by
  rcases h with ⟨x, ⟨h1, h2⟩⟩
  by_cases h3 : b + c + 1 = 0
  · -- Assume b + c + 1 = 0
    left
    linarith
  · -- Assume b + c + 1 ≠ 0
    have eq4 : x ^ 3 = 1 := by
      have eq5 : b * x ^ 2 + c * x + 1 = 0 := h2
      have eq6 : x^2 + b * x + c = 0 := h1
      have eq7 : c = -x^2 - b * x := by linarith
      rw [eq7] at eq5
      have eq8 : x ^ 3 = 1 := by
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x), sq_nonneg (x - 1)]
      linarith
    have eq8 : x = 1 := by
      have h3 : x ^ 3 = 1 := eq4
      have h4 : x^3 - 1 = 0 := by linarith
      have h5 : (x - 1) * (x^2 + x + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h5) with h6 h7
      · -- x - 1 = 0
        linarith
      · -- x^2 + x + 1 = 0
        nlinarith [sq_nonneg (x + 1 / 2)]
    have eq9 : b + c + 1 = 0 := by
      have eq8' : x = 1 := eq8
      rw [eq8'] at h1
      linarith
    exfalso
    apply h3
    linarith