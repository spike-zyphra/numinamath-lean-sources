import Mathlib

theorem algebra_22074 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 3 + 3 * x ^ 2 + 1) : {(a, b) : ℝ×ℝ | a ≠ 0 ∧ ∀x, f x - f a = (x - a) ^ 2 * (x - b)} = {(-2, 1)} := by
  ext ⟨a, b⟩
  simp [-mul_add, -add_mul]
  constructor
  · -- First direction: if pair (a,b), non-zero a and polynomial, give pair
    rintro ⟨ha, heq⟩
    have eq1 := heq 0
    simp [hf] at eq1
    have eq2 : b = a + 3 := by
      apply (mul_left_inj' (show a ^ 2 ≠ 0 by
        intro ha'
        have : a = 0 := by
          nlinarith
        tauto
      )).mp
      nlinarith
    have eq3 := heq 1
    simp [hf] at eq3
    rw [eq2] at eq3
    have eq4 : a ^ 2 + a - 2 = 0 := by
      nlinarith [eq3]
    have eq5 : (a - 1) * (a + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq5) with ha1 ha2
    · -- Case a = 1, contradiction
      have eq6 := heq (-1)
      simp [hf] at eq6
      rw [eq2] at eq6
      nlinarith [ha1, eq6]
    · -- Case a = -2
      have ha2' : a = -2 := by linarith
      have hb2 : b = 1 := by
        rw [ha2'] at eq2
        linarith
      simp [ha2', hb2]
  · -- Backward direction: pair works satisfies the above
    rintro ⟨rfl, rfl⟩
    constructor
    · -- Show a ≠ 0
      norm_num
    · -- Show the equation holds for all x
      intro x
      simp [hf]
      ring_nf