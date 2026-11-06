import Mathlib

theorem algebra_261412 {a b c d : ℝ} (P : ℝ → ℝ) (hP : ∀ x, P x = a * x^3 + b * x^2 + c * x + d)
    (hP' : ∀ x, |x| ≤ 1 → |P x| ≤ 1) : |a| + |b| + |c| + |d| ≤ 7 := by

  have h1 := hP' 1 (by norm_num [abs_le])
  simp [hP] at h1

  have h2 := hP' (-1) (by norm_num [abs_le])
  simp [hP] at h2

  have h3 := hP' (0 : ℝ) (by norm_num [abs_le])
  simp [hP] at h3

  have h4 := hP' (1 / 2 : ℝ) (by norm_num [abs_le])
  simp [hP] at h4

  have h5 := hP' (-1 / 2 : ℝ) (by norm_num [abs_le])
  simp [hP] at h5

  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  cases' abs_le.mp h4 with h4_neg h4_pos
  cases' abs_le.mp h5 with h5_neg h5_pos

  cases' abs_cases a with ha ha <;> cases' abs_cases b with hb hb <;> 
    cases' abs_cases c with hc hc <;> cases' abs_cases d with hd hd <;> 
      all_goals
        linarith