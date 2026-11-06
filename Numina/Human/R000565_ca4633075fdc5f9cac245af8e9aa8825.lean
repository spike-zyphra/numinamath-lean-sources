import Mathlib

/-What is the sum of the 2009 fractions of the form $\frac{2}{n(n+2)}$ if the values of $n$ are the positive integers from 1 through 2009? Express your answer as a decimal to the nearest thousandth.-/
theorem algebra_12632 :
    (⌊((∑ n ∈ (Finset.Icc 1 2009 : Finset ℕ), (2 / (n * (n + 2)) : ℝ)) * 1000 + 1 / 2)⌋ / 1000 : ℝ) = 1.499 := by
  -- simplify the conclusion to 1 + 1 / 2 - 1 / 2010 - 1 / 2011
  suffices h : ∑ n ∈ (Finset.Icc 1 2009 : Finset ℕ), (2 / (n * (n + 2)) : ℝ) = 1 + 1 / 2 - 1 / 2010 - 1 / 2011 by
    field_simp [h]
    norm_num
  -- convert the Icc to Ico, so that we have plenty of theorems to use
  have set_eq : (Finset.Icc 1 2009 : Finset ℕ) = (Finset.Ico 1 2010 : Finset ℕ) := by
    ext n
    simp
    intro _
    apply Iff.intro <;> intro h
    linarith only [h]
    linarith only [h]
  -- show that 2 / (n * (n + 2)) = 1 / n - 1 / (n + 2)
  have eq₁ (n : ℕ) (hn : 0 < (n : ℝ)) : 2 / ((n : ℝ) * (n + 2)) = 1 / (n : ℝ) - 1 / ((n : ℝ) + 2) := by
    rw [div_sub_div]
    ring_nf
    linarith only [hn]
    linarith only [hn]
  -- set function to simplify the calculation
  set f := fun n : ℕ => (1 : ℝ) / (n + 1) with hf
  set g := fun n : ℕ => (1 : ℝ) / (n + 2) with hg
  -- do the calculation
  calc
    ∑ n ∈ (Finset.Icc 1 2009 : Finset ℕ), 2 / ((n : ℝ) * (n + 2)) = ∑ n ∈ (Finset.Icc 1 2009 : Finset ℕ), (1 / (n : ℝ) - 1 / ((n : ℝ) + 2)) := by rw [Finset.sum_congr]; rfl; intro x hx; rw [eq₁ x]; simp at hx; norm_num; linarith only [hx]
    _ = ∑ n ∈ (Finset.Ico 1 2010 : Finset ℕ), (1 / (n : ℝ) - 1 / ((n : ℝ) + 2)) := by rw [set_eq]
    _ = ∑ n ∈ (Finset.range (2010 - 1) : Finset ℕ), (1 / ((1 + n) : ℝ) - 1 / ((((1 + n) : ℝ)) + 2)) := by rw [Finset.sum_Ico_eq_sum_range]; rw [Finset.sum_congr]; rfl; intro x _; norm_num
    _ = ∑ n ∈ (Finset.range 2009 : Finset ℕ), ((1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) + (1 / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 3))) := by rw [Finset.sum_congr]; rfl; intro x _; ring_nf
    _ = ∑ n ∈ (Finset.range 2009 : Finset ℕ), (f n  - f (n + 1) + (g n - g (n + 1))) := by rw [Finset.sum_congr]; rfl; intro x _; rw [hf, hg]; field_simp; ring_nf
    _ = ∑ n ∈ (Finset.range 2009 : Finset ℕ), (f n - f (n + 1)) + ∑ n ∈ (Finset.range 2009 : Finset ℕ), (g n - g (n + 1)) := by rw [Finset.sum_add_distrib]
    _ = (f 0 - f 2009) + (g 0 - g 2009) := by rw [Finset.sum_range_sub', Finset.sum_range_sub']
    _ = 1 + 1 / 2 - 1 / 2010 - 1 / 2011 := by ring_nf
    