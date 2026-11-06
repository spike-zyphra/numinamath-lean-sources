import Mathlib

theorem algebra_248614 (a b c d : ℝ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : b ≠ c) (h₄ : b ≠ d) (h₅ : c ≠ d) (h₆ : a^2 - 3 * c * a - 8 * d = 0)
    (h₇ : b^2 - 3 * c * b - 8 * d = 0) (h₈ : c^2 - 3 * a * c - 8 * b = 0)
    (h₉ : d^2 - 3 * a * d - 8 * b = 0) :
    a + b + c + d = 96 := by

  have eq1 : a + b = 3 * c := by
    have eq2 : a^2 - 3 * c * a - 8 * d = 0 := h₆
    have eq3 : b^2 - 3 * c * b - 8 * d = 0 := h₇
    have eq4 : a^2 - b^2 - 3 * c * (a - b) = 0 := by
      linarith [eq2, eq3]
    have eq5 : (a - b) * (a + b - 3 * c) = 0 := by
      ring_nf at eq4 ⊢
      linarith
    cases' (mul_eq_zero.mp eq5) with h10 h11
    · -- Case a - b = 0, so a = b
      exfalso
      apply h₀
      linarith
    · -- Case a + b - 3c = 0
      linarith

  have eq2 : c + d = 3 * a := by
    have eq3 : c^2 - 3 * a * c - 8 * b = 0 := h₈
    have eq4 : d^2 - 3 * a * d - 8 * b = 0 := h₉
    have eq5 : c^2 - d^2 - 3 * a * (c - d) = 0 := by
      linarith [eq3, eq4]
    have eq6 : (c - d) * (c + d - 3 * a) = 0 := by
      ring_nf at eq5 ⊢
      linarith
    cases' (mul_eq_zero.mp eq6) with h10 h11
    · -- Case c - d = 0, so c = d
      exfalso
      apply h₅
      linarith
    · -- Case c + d - 3a = 0
      linarith

  have eq3 : b = 3 * c - a := by linarith [eq1]
  have eq4 : d = 3 * a - c := by linarith [eq2]

  have eq5 : a ^ 2 - 3 * a * c - 24 * a + 8 * c = 0 := by
    rw [show d = 3 * a - c by linarith [eq4] ] at h₆
    nlinarith

  have eq6 : c ^ 2 - 3 * a * c - 24 * c + 8 * a = 0 := by
    rw [show b = 3 * c - a by linarith [eq3] ] at h₈
    nlinarith

  have eq7 : (a ^ 2 - 3 * a * c - 24 * a + 8 * c) - (c ^ 2 - 3 * a * c - 24 * c + 8 * a) = 0 := by
    linarith [eq5, eq6]

  have eq8 : (a - c) * (a + c - 32) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp eq8) with h10 h11
  · -- Case a - c = 0, so a = c
    exfalso
    apply h₁
    linarith
  · -- Case a + c - 32 = 0
    have eq9 : a + c = 32 := by linarith

    have eq10 : b + d = 2 * (a + c) := by
      nlinarith [eq1, eq2, eq3, eq4]

    have eq11 : b + d = 64 := by
      rw [show a + c = 32 by linarith [eq9] ] at eq10
      linarith

    nlinarith [eq9, eq11]