import Mathlib
open Real
/- Find $\log _{n}\left(\frac{1}{2}\right) \log _{n-1}\left(\frac{1}{3}\right) \cdots \log _{2}\left(\frac{1}{n}\right)$ in terms of $n$. -/
theorem algebra_610840 (n : ℕ) (hn : n ≥ 2) : ∏ i in Finset.range (n - 1), (logb ((n : ℝ) - i) (1 / (i + 2))) = (-1) ^ (n - 1):= by

  -- Convert each logarithm term using the change of base formula
  have h1 : ∀ i ∈ Finset.range (n - 1), logb ((n : ℝ) - i) (1 / (i + 2)) = (-log (i + 2) / log (n - i)):= by
    intro i _
    rw [←Real.log_div_log]
    simp

  -- Apply the conversion to the entire product
  replace h1 : ∏ i in Finset.range (n - 1), logb ((n : ℝ) - i) (1 / (i + 2)) = ∏ i in Finset.range (n - 1), ((-log (i + 2) / log (n - i))):= by exact Finset.prod_congr rfl h1
  rw [h1]
  simp

  -- Prove that product of negative logarithms equals (-1)^k times product of positive logarithms
  have h2 : ∀ k : ℕ,  ∏ x ∈ Finset.range k, -log (↑x + 2) = (-1) ^ k * ∏ x ∈ Finset.range k, log (↑x + 2):= by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.prod_range_succ, ih]
      rw [Finset.prod_range_succ]
      rw [show (-1 : ℝ) ^ (k + 1) = (-1) * (-1) ^ k by ring_nf]
      linarith

  rw [h2 (n - 1)]

  -- Define helper function for logarithm terms
  set f:= fun x : ℕ => log (↑n - ↑x) with hf

  -- Flip the product using index transformation
  have h3 : (Finset.range (n - 2 + 1)).prod f = ∏ i in Finset.range (n - 2 + 1), f (n - 1 - 1 - i):= by exact Eq.symm (Finset.prod_flip f)
  rw [show n - 2 + 1 = n - 1 by omega] at h3
  rw [show n - 1 - 1 = n - 2 by omega] at h3
  rw [h3]
  simp [hf]

  -- Prove equality of logarithm terms after index transformation
  have h4 : ∀ i ∈ Finset.range (n - 1), log (↑n - ↑(n - 2 - i)) = log (↑i + 2):= by
    intro i hi
    simp at hi
    have h4 : n - 2 - i + 2 + i = n:= by omega
    rify at h4
    rw [show (↑n : ℝ) - ↑(n - 2 - i) = ↑i + 2 by linarith]

  -- Apply the equality to the entire product
  replace h4 : ∏ i in Finset.range (n - 1), log (↑n - ↑(n - 2 - i)) = ∏ i in Finset.range (n - 1), log (↑i + 2):= by exact Finset.prod_congr rfl h4
  rw [h4]

  -- Prove that the product of logarithms is positive
  have h5 : ∏ i in Finset.range (n - 1), log (↑i + 2) > 0:= by
    have h5 : ∀ i ∈ Finset.range (n - 1), log (↑i + 2) > 0:= by
      intro i _
      have h5 : i + 2 > 1:= by linarith
      rify at h5
      exact log_pos h5
    exact Finset.prod_pos h5
  field_simp
