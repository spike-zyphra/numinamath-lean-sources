import Mathlib

open Finset Real

-- The sum of the first k even numbers is k * (k + 1)
lemma l_sum_even {k : ℕ} : ∑ j ∈ range k, (2 * j + 2) = k * (k + 1) := by
  -- Use induction on k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

-- The sum of the first k odd numbers is k ^ 2
lemma l_sum_odd {k : ℕ} : ∑ j ∈ range k, (2 * j + 1) = k ^ 2 := by
  -- Use induction on k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

lemma l_prod_telescope {k : ℕ} : ∏ i ∈ range k, (i + 2 : ℝ) / (i + 1) = k + 1 := by
  -- Use induction on k
  induction k with
  | zero => simp
  | succ k ih =>
    -- Split off a term and use the induction hypothesis
    rw [prod_range_succ, ih, mul_div_cancel₀ _ (by norm_cast)]
    simp
    linarith

-- The product of sqrt is sqrt of a product
lemma l_prod_sqrt {f : ℕ → ℝ} {k : ℕ} (h : ∀ i ∈ range k, 0 ≤ f i) : ∏ i ∈ range k, sqrt (f i) = sqrt (∏ i ∈ range k, f i) := by
  -- Use induction on k
  induction k with
  | zero => simp
  | succ k ih =>
    -- The condition for the previous case still holds
    have : ∀ i ∈ range k, 0 ≤ f i := by intro i hi; simp at *; apply h; linarith
    specialize ih this
    -- Simplify the product
    rw [prod_range_succ, ih, ← sqrt_mul (by apply prod_nonneg; tauto) _, ← prod_range_succ]

/- Subject 1. Show that $\sqrt{\frac{2}{1}} \cdot \sqrt{\frac{2+4}{1+3}} \cdot \sqrt{\frac{2+4+6}{1+3+5}} \cdot \ldots \cdot \sqrt{\frac{2+4+6+\ldots+2016}{1+3+5+\ldots+2015}}$ is an irrational number. -/
theorem number_theory_119463 : Irrational (∏ i ∈ Finset.range 1008, sqrt ((∑ j ∈ Finset.range (i + 1), (2 * j + 2)) / (∑ j ∈ Finset.range (i + 1), (2 * j + 1)))) := by
  -- Using the first two lemmas, we can rewrite the numerator and denominator
  conv =>
    rhs
    congr
    · skip
    intro i
    -- Rewrite sums
    rw [l_sum_even, l_sum_odd, pow_two]
    simp
    -- Cancel the common term
    rw [mul_div_mul_left _ _ (by positivity), add_assoc]
    norm_num
  -- Take the sqrt on the outside and telescope
  rw [l_prod_sqrt (by intro i hi; positivity), l_prod_telescope]
  norm_num
  -- √1009 is irrational iff 1009 is not a perfect square
  rw [irrational_sqrt_ofNat_iff]
  unfold IsSquare
  push_neg
  -- Suppose we have an r such that r * r = 1009
  intro r hr
  -- Then r < 32
  have : r < 32 := by nlinarith
  -- But all r < 32 does not work by inspection, a contradiction.
  interval_cases r <;> simp at *