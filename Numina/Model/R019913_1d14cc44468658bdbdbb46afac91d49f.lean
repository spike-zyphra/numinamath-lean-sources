import Mathlib

open Real

theorem algebra_12911 {f : ℕ → ℝ → ℝ} (hf : ∀ x, f 1 x = sqrt (x ^ 2 + 1))
    (hfn : ∀ n > 0, f (n + 1) = f 1 ∘ f n) :
    f 2020 96 = 106 := by

  have f1 : ∀ n, f (n + 1) 96 = Real.sqrt (9216 + n + 1 : ℝ) := by
    intro n 
    induction n with 
    | zero =>
      simp [hf]
      all_goals norm_num
    | succ n ih =>
      have eq1 : f (n + 2) 96 = f 1 (f (n + 1) 96) := by
        rw [hfn (n + 1) (by linarith)]
        simp [Function.comp_apply]
      rw [eq1]
      rw [hf]
      rw [ih]
      field_simp
      <;> ring_nf <;> norm_num
      <;> ring_nf
      <;> norm_num 
  have h_eq : f 2020 96 = Real.sqrt (9216 + 2019 + 1 : ℝ) := f1 2019
  rw [h_eq]
  have h2 : (9216 + 2019 + 1 : ℝ) = (11236 : ℝ) := by norm_num
  rw [h2]
  have h3 : Real.sqrt (11236 : ℝ) = (106 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h3]
  all_goals norm_num