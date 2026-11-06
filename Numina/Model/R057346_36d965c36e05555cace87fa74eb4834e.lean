import Mathlib

theorem algebra_111090 (a : ℝ) (ha : 0 < a ∧ a < 1 / 2) (M N P Q : ℝ)
    (hM : M = 1 - a ^ 2) (hN : N = 1 + a ^ 2) (hP : P = 1 / (1 - a))
    (hQ : Q = 1 / (1 + a)) : Q < M ∧ M < N ∧ N < P := by

  rcases ha with ⟨ha_pos, ha_lt⟩
  have h1 : Q < M := by
    rw [hQ, hM]
    have h2 : 0 < 1 + a := by linarith
    apply (div_lt_iff (by linarith)).mpr
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2), sq_nonneg (a), sq_nonneg (a - 1 / 4)]

  have h2 : M < N := by
    rw [hM, hN]
    nlinarith

  have h3 : N < P := by
    rw [hN, hP]
    have h6 : 0 < 1 - a := by linarith
    apply (lt_div_iff (by linarith)).mpr
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2), sq_nonneg (a), sq_nonneg (a - 1 / 4)]

  exact ⟨h1, h2, h3⟩