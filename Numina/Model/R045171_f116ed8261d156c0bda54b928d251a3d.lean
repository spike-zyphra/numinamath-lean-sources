import Mathlib

theorem algebra_3843 (f : ℝ → ℝ) (hf : f = fun x => (9 : ℝ)^(x^3 - 3 * x^2 - 28 * x + 60) - 1) : ∑ᶠ x ∈ {x | f x = 0}, x = 3 := by
  have h1 : {x | f x = 0} = {2, -5, 6} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f(x) = 0, prove x ∈ {2, -5, 6}
      intro h_eq
      have h_eq1 : (9 : ℝ) ^ (x ^ 3 - 3 * x ^ 2 - 28 * x + 60) = 1 := by
        linarith
      have h_eq2 : x ^ 3 - 3 * x ^ 2 - 28 * x + 60 = (0 : ℝ) := by
        apply_fun (Real.logb (9 : ℝ)) at h_eq1
        have h3 : Real.logb (9 : ℝ) ((9 : ℝ) ^ (x ^ 3 - 3 * x ^ 2 - 28 * x + 60)) = x ^ 3 - 3 * x ^ 2 - 28 * x + 60 := by
          rw [Real.logb_rpow]
          all_goals norm_num
        have h4 : Real.logb (9 : ℝ) (1 : ℝ) = 0 := by
          simp [Real.logb_one]
        rw [h3] at h_eq1
        rw [h4] at h_eq1
        linarith
      have h_eq3 : (x - 2) * (x ^ 2 - x - 30) = 0 := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 6), sq_nonneg (x + 5), sq_nonneg (x - 2), sq_nonneg (x + 5 - 6)]
      cases' (mul_eq_zero.1 h_eq3) with h_eq4 h_eq5
      · -- x - 2 = 0
        left
        linarith
      · -- x^2 - x - 30 = 0
        have h_eq6 : x ^ 2 - x - 30 = 0 := by linarith
        have h_eq7 : (x - 6) * (x + 5) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h_eq7) with h_eq8 h_eq9
        · -- x - 6 = 0
          right
          right
          linarith
        · -- x + 5 = 0
          right
          left
          linarith
    · -- Assume x ∈ {2, -5, 6}, prove f(x) =0
      rintro (rfl | rfl | rfl)
      · -- x = 2
        norm_num
      · -- x = -5
        norm_num
      · -- x = 6
        norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> norm_num