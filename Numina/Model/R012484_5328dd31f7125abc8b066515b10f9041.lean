import Mathlib

theorem algebra_261493 {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = x k + 1 / 2)
    (hx1 : x 1 = 1) (n : ℕ) :
    ∑ i in Finset.Icc 1 n, x i = (n ^ 2 + 3 * n) / 4 := by

  have h1 : x 0 = 1 / 2 := by
    have eq1 := hx 0
    norm_num at eq1
    linarith [hx1, eq1]

  have eq1 : ∀ i : ℕ, x i = (i + 1 : ℝ) / 2 := by
    intro i
    induction i with 
    | zero =>
      simp [h1]
      <;> norm_num
    | succ i ih =>
      have eq2 := hx i
      simp [ih] at eq2 ⊢
      linarith
      <;> norm_num
  
  have eq2 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, x i = (n ^ 2 + 3 * n) / 4 := by
    intro n
    induction n with 
    | zero =>
      simp 
      <;> norm_num 
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [eq1 (n + 1)]
      rw [ih]
      field_simp at *
      ring_nf
      <;> norm_num 
      <;> linarith
  specialize eq2 n
  simpa using eq2
  <;> norm_num
  <;> norm_num