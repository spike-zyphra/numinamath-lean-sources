import Mathlib

theorem algebra_8603 {a b c : ℕ → ℝ} (ha : ∀ n, a (n + 1) - a n = b n)
    (hb : ∀ n, b (n + 1) - b n = c n) (hc : ∀ n, c n = 20) (h10 : a 10 = 23) (h20 : a 20 = 23) :
    a 30 = 2023 := by

  have eq1 : ∀ n, b (n + 1) = b n + 20 := by
    intro n 
    have eq2 : b (n + 1) - b n = c n := hb n
    have eq3 : c n = 20 := hc n
    linarith

  have eq2 : ∀ n, b n = b 0 + (n : ℝ) * 20 := by
    intro n
    induction n with 
    | zero =>
      simp
    | succ n ih =>
      have : b (n + 1) = b n + 20 := eq1 n 
      rw [this, ih]
      simp [add_mul, mul_add]
      <;> ring

  have eq3 : ∀ n, a n = a 0 + (n : ℝ) * b 0 + 10 * ( (n : ℝ) ) * ( (n : ℝ) - 1 ) := by
    intro n
    induction n with 
    | zero =>
      simp
    | succ n ih =>
      have eq5 : a (n + 1) = a n + b n := by
        have : a (n + 1) - a n = b n := ha n
        linarith
      rw [eq5]
      rw [ih]
      simp [eq2 n]
      ring

  have eq4 : a 10 = a 0 + (10 : ℝ) * b 0 + 10 * ( (10 : ℝ) ) * ( (10 : ℝ) - 1 ) := eq3 10
  have eq5 : a 20 = a 0 + (20 : ℝ) * b 0 + 10 * ( (20 : ℝ) ) * ( (20 : ℝ) - 1 ) := eq3 20 
  rw [h10] at eq4 
  rw [h20] at eq5 
  have ha0 : a 0 = 2023 := by
    norm_num at eq4 eq5
    linarith

  have hb0 : b 0 = -290 := by 
    norm_num at eq4 eq5 
    nlinarith [eq4, eq5, ha0]

  have eq6 : a 30 = a 0 + (30 : ℝ) * b 0 + 10 * ( (30 : ℝ) ) * ( (30 : ℝ) - 1 ) := eq3 30 
  rw [ha0, hb0] at eq6 
  norm_num at eq6 ⊢
  linarith