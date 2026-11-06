import Mathlib
/- Prove that the product of the 99 numbers of the form $\frac{k^{3}-1}{k^{3}+1}$ where $k=2,3, \ldots, 100$, is greater than $\frac{2}{3}$. -/
theorem algebra_240729 : ∏ k ∈ (Finset.Icc 2 100 : Finset ℕ), (k ^ 3 - (1 : ℝ)) / (k ^ 3 + 1) > 2 / 3:= by

  -- Define a helper lemma using induction
  -- For any natural number n, prove that the product from k=2 to k=(2+n) equals:
  -- 2/3 * ((n+2)²+n+3) / ((n+2)(n+3))
  have h1 : ∀ n : ℕ, ∏ k ∈ (Finset.Icc 2 (2 + n) : Finset ℕ), (k ^ 3 - (1 : ℝ)) / (k ^ 3 + 1) = 2 / 3 * (((↑n : ℝ) + 2) ^ 2 + n + 2 + 1) / ((n + 2) * (n + 3)):= by
    intro n
    induction n with
    -- Base case: n = 0
    | zero =>
      simp
      field_simp
      linarith
    -- Inductive step: n → n+1
    | succ n ih =>
      rw [show 2 + (n + 1) = (2 + n) + 1 by ring]
      rw [Finset.prod_Icc_succ_top, ih]
      field_simp
      linarith
      omega

  -- Apply the helper lemma with n = 98 to get the result for k=2 to k=100
  specialize h1 98
  rw [show 2 + 98 = 100 by ring] at h1
  rw [h1]
  field_simp
  norm_num
