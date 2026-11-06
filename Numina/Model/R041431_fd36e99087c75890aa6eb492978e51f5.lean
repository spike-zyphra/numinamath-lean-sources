import Mathlib

theorem algebra_134832 (x : ℝ) :
    2 * (Real.sin x) ^ 2 + 1 = Real.cos (Real.sqrt 2 * x) ↔ x = 0 := by
  constructor
  · -- Assume $2 \sin^2 x + 1 = \cos(\sqrt{2} x)$, prove $x = 0$.
    intro h
    have h1 : 2 * (Real.sin x) ^ 2 + 1 ≥ 1 := by
      nlinarith [Real.sin_sq_le_one x]
    have h2 : Real.cos (Real.sqrt 2 * x) ≤ 1 := by
      apply Real.cos_le_one
    have h3 : Real.cos (Real.sqrt 2 * x) = 1 := by
      nlinarith [h, h1, h2]
    have h4 : 2 * (Real.sin x) ^ 2 + 1 = 1 := by
      nlinarith [h, h3]
    have h5 : Real.sin x = 0 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    have h7 : Real.sin x = 0 := h5
    have h8 : ∃ k : ℤ, Real.sqrt 2 * x = (k : ℝ) * (2 * Real.pi) := by
      rw [Real.cos_eq_one_iff] at h3
      rcases h3 with ⟨k, hk⟩
      use k
      all_goals linarith
    rcases h8 with ⟨k, hk⟩
    have h9 : ∃ m : ℤ, x = (m : ℝ) * Real.pi := by
      have h77 : Real.sin x = 0 := h5
      obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 h77
      use m
      linarith
    rcases h9 with ⟨m, hm⟩
    have h10 : Real.sqrt 2 * (m * Real.pi) = (k : ℝ) * (2 * Real.pi) := by
      have hk0 : Real.sqrt 2 * x = (k : ℝ) * (2 * Real.pi) := by
        linarith [hk]
      rw [hm] at hk0
      linarith
    have h11 : Real.sqrt 2 * (m : ℝ) = (2 * (k : ℝ)) := by
      have h11 : Real.pi ≠ 0 := Real.pi_ne_zero
      apply (mul_left_inj' (show Real.pi ≠ 0 by exact Real.pi_ne_zero)).mp
      linarith
    by_cases h13 : m ≠ 0
    · -- Assume m ≠ 0
      have h14 : Real.sqrt 2 = (2 * (k : ℝ)) / (m : ℝ) := by
        field_simp [(show (m : ℝ) ≠ 0 by exact_mod_cast (show m ≠ (0 : ℤ) by simpa using h13))]
        linarith
      have h15 : Irrational (Real.sqrt 2 : ℝ) := by
        apply irrational_sqrt_two
      have h16 : ¬ Irrational (Real.sqrt 2 : ℝ) := by
        rw [h14]
        simp
      contradiction
    · -- m = 0
      have h17 : m = 0 := by
        omega
      have h18 : x = 0 := by
        rw [hm]
        rw [show (m : ℝ) = (0 : ℝ) by exact_mod_cast h17]
        norm_num
      linarith
  · -- Assume x = 0, prove 2 * (Real.sin x) ^ 2 + 1 = Real.cos (Real.sqrt 2 * x).
    intro h
    rw [h]
    have h1 : Real.sin (0 : ℝ) = 0 := by simp
    have h2 : Real.cos (Real.sqrt 2 * (0 : ℝ)) = 1 := by
      simp
    simp [h1, h2]
    all_goals nlinarith