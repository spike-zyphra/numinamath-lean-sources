import Mathlib

theorem algebra_142390 (f : ℝ → ℝ) (m : ℝ) (hf : f = fun x => x^2 + m * x + 3) :
    f 0 = 2 ∨ f (-m / 2) = 2 ∨ f (m / 2) = 2 ↔ m = 2 ∨ m = -2 := by
  constructor
  · -- Assume $f(0) = 2 ∨ f(-m / 2) = 2 ∨ f(m / 2) = 2$, prove $m = 2 ∨ m = -2$.
    intro h
    rcases h with (h | h | h)
    · -- Assume f 0 = 2.
      have h1 : f 0 = 0 ^ 2 + m * 0 + 3 := by
        rw [hf]
      rw [h1] at h
      all_goals nlinarith
    · -- Assume $f(-m / 2) = 2$.
      have h2 : f (-m / 2) = (-m / 2) ^ 2 + m * (-m / 2) + 3 := by
        rw [hf]
      rw [h2] at h
      have h_eq : m ^2 = 4 := by
        nlinarith
      have : m = 2 ∨ m = -2 := by
        have h3 : m ^2 - 4 = 0 := by linarith
        have h4 : (m - 2) * (m + 2) = 0 := by
          linarith
        cases' (mul_eq_zero.1 h4) with h5 h6
        · -- Assume $m - 2 = 0$.
          left
          linarith
        · -- Assume $m + 2 = 0$.
          right
          linarith
      tauto
    · -- Assume $f(m / 2) = 2$.
      have h3 : f (m / 2) = (m / 2) ^ 2 + m * (m / 2) + 3 := by
        rw [hf]
      rw [h3] at h
      nlinarith [sq_nonneg m]
  · -- Assume m = 2 ∨ m = -2.
    rintro (hm | hm)
    · -- Assume m = 2.
      have hm2 : m = 2 := hm
      right
      left
      rw [hm2]
      simp [hf]
      all_goals norm_num [hm2]
    · -- Assume m = -2.
      have hm2 : m = -2 := hm
      right
      left
      rw [hm2]
      simp [hf]
      all_goals norm_num [hm2]