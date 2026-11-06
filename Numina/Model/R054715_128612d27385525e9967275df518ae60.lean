import Mathlib

theorem algebra_251051 {x y : ℝ} (h₀ : 1 / x - 1 / y = 1 / 2) (h₁ : y - x = 1) :
    (x + y) ^ 2 = 9 := by
  have h2 : y = x + 1 := by linarith
  rw [h2] at h₀
  have hx1 : x ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num at h₀
    all_goals
      try tauto
  have hx2 : x + 1 ≠ 0 := by
    by_contra h
    have h_zero : x + 1 = 0 := h
    have h_zero_subst : x = -1 := by linarith
    rw [h_zero_subst] at h₀
    norm_num at h₀
    all_goals
      try tauto
  field_simp [(show x ≠ 0 by exact hx1), (show x + 1 ≠ 0 by
    try { tauto }
  )] at h₀
  have h3 : x * (x + 1) = 2 := by
    nlinarith
  have h4 : x ^ 2 + x - 2 = 0 := by
    nlinarith
  have h5 : (x - 1) * (x + 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- Case where x = 1.
    have hx11 : x = 1 := by linarith
    have hy11 : y = 2 := by linarith [h2, hx11]
    rw [hx11, hy11]
    norm_num
  · -- Case where x + 2 = 0, so x = -2.
    have hx22 : x = -2 := by linarith
    have hy11 : y = -1 := by linarith [h2, hx22]
    rw [hx22, hy11]
    norm_num
  all_goals
    try tauto
    <;> try { norm_num <;> tauto <;> try { nlinarith } }
    <;> try { nlinarith }