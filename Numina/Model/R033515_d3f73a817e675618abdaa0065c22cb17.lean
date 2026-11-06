import Mathlib

theorem algebra_205443 {x : ℕ → ℝ} (hx1 : x 1 = 3) (hxn : ∀ n, ∑ i in Finset.Icc 1 (n - 1), x i + 4 / 3 * x n = 4) :
    x 2015 = 3 / 4 ^ 2014 := by

  have h1 : ∀ n, x (n + 1) = 3 / 4 ^ n := by
    intro n
    induction n with
    | zero => 
      norm_num [hx1]
    | succ n ih =>
      have eq1 := hxn (n + 1)
      have eq2 := hxn (n + 2)
      norm_num [Finset.sum_Icc_succ_top, hx1] at eq1 eq2 
      have eq3 : x (n + 2) = x (n + 1) / 4 := by
        nlinarith
      rw [eq3]
      rw [ih]
      field_simp
      ring_nf
      <;> norm_num
  have h1' : x 2015 = 3 / 4 ^ 2014 := by
    specialize h1 2014
    norm_num at h1 ⊢
    linarith
  exact h1'