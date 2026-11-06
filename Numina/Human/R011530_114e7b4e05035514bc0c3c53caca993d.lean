import Mathlib
/- II. (50 points) Let $x_{i} \in \mathbf{R}_{+}(i=1,2,3,4,5)$. Find the minimum value of $f=\frac{x_{1}+x_{3}}{x_{5}+2 x_{2}+3 x_{4}}+\frac{x_{2}+x_{4}}{x_{1}+2 x_{3}+3 x_{5}}+$ $\frac{x_{3}+x_{5}}{x_{2}+2 x_{4}+3 x_{1}}+\frac{x_{4}+x_{1}}{x_{3}+2 x_{5}+3 x_{2}}+\frac{x_{5}+x_{2}}{x_{4}+2 x_{1}+3 x_{3}}$. -/
theorem number_theory_145783 : IsLeast {f : ℝ | ∃ x1 x2 x3 x4 x5 : ℝ, x1 > 0 ∧ x2 > 0 ∧ x3 > 0 ∧ x4 > 0 ∧ x5 > 0 ∧ f = (x1 + x3) / (x5 + 2 * x2 + 3 * x4) + (x2 + x4) / (x1 + 2 * x3 + 3 * x5) + (x3 + x5) / (x2 + 2 * x4 + 3 * x1) + (x4 + x1) / (x3 + 2 * x5 + 3 * x2) + (x5 + x2) / (x4 + 2 * x1 + 3 * x3)} (5 / 3):= by
  constructor
  -- First, we prove that 5/3 is in the set by showing f(1,1,1,1,1) = 5/3
  .
    use 1, 1, 1, 1, 1
    norm_num
  -- Next, we prove that 5/3 is the minimum value
  .
    intro f
    simp
    intro x1 hx1 x2 hx2 x3 hx3 x4 hx4 x5 hx5 hf
    subst f
    -- Define function f as the square root of each term in the original sum
    set f : ℕ → ℝ:= fun i => if i = 0 then √((x1 + x3) / (x5 + 2 * x2 + 3 * x4)) else if i = 1 then √((x2 + x4) / (x1 + 2 * x3 + 3 * x5)) else if i = 2 then √((x3 + x5) / (x2 + 2 * x4 + 3 * x1)) else if i = 3 then √((x4 + x1) / (x3 + 2 * x5 + 3 * x2)) else √((x5 + x2) / (x4 + 2 * x1 + 3 * x3)) with hf
    -- Define function g as the square root of the product of numerator and denominator for each term
    set g : ℕ → ℝ:= fun i => if i = 0 then √((x5 + 2 * x2 + 3 * x4) * (x1 + x3)) else if i = 1 then √((x1 + 2 * x3 + 3 * x5) * (x2 + x4)) else if i = 2 then √((x2 + 2 * x4 + 3 * x1) * (x3 + x5)) else if i = 3 then √((x3 + 2 * x5 + 3 * x2) * (x4 + x1)) else √((x4 + 2 * x1 + 3 * x3) * (x5 + x2)) with hg
    clear_value f g
    -- Apply Cauchy-Schwarz inequality
    have h : (∑ i ∈ Finset.range 5, f i * g i) ^ 2 ≤ (∑ i ∈ Finset.range 5, f i ^ 2) * ∑ i ∈ Finset.range 5, g i ^ 2:= by exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range 5) f g
    -- Calculate the sum of f(i)*g(i) across all i
    have h1 : ∑ i ∈ Finset.range 5, f i * g i = 2 * (x1 + x2 + x3 + x4 + x5):= by
      simp [Finset.sum_range_succ, hf, hg]
      rw [show √((x1 + x3) / (x5 + 2 * x2 + 3 * x4)) * √((x5 + 2 * x2 + 3 * x4) * (x1 + x3)) = √((x1 + x3) / (x5 + 2 * x2 + 3 * x4) * ((x5 + 2 * x2 + 3 * x4) * (x1 + x3))) by field_simp]
      rw [show √((x2 + x4) / (x1 + 2 * x3 + 3 * x5)) * √((x1 + 2 * x3 + 3 * x5) * (x2 + x4)) = √((x2 + x4) / (x1 + 2 * x3 + 3 * x5) * ((x1 + 2 * x3 + 3 * x5) * (x2 + x4))) by field_simp]
      rw [show √((x3 + x5) / (x2 + 2 * x4 + 3 * x1)) * √((x2 + 2 * x4 + 3 * x1) * (x3 + x5)) = √((x3 + x5) / (x2 + 2 * x4 + 3 * x1) * ((x2 + 2 * x4 + 3 * x1) * (x3 + x5))) by field_simp]
      rw [show √((x4 + x1) / (x3 + 2 * x5 + 3 * x2)) * √((x3 + 2 * x5 + 3 * x2) * (x4 + x1)) = √((x4 + x1) / (x3 + 2 * x5 + 3 * x2) * ((x3 + 2 * x5 + 3 * x2) * (x4 + x1))) by field_simp]
      rw [show √((x5 + x2) / (x4 + 2 * x1 + 3 * x3)) * √((x4 + 2 * x1 + 3 * x3) * (x5 + x2)) = √((x5 + x2) / (x4 + 2 * x1 + 3 * x3) * ((x4 + 2 * x1 + 3 * x3) * (x5 + x2))) by field_simp]
      rw [show (x1 + x3) / (x5 + 2 * x2 + 3 * x4) * ((x5 + 2 * x2 + 3 * x4) * (x1 + x3)) = (x1 + x3) ^ 2 by field_simp ; linarith]
      rw [show (x2 + x4) / (x1 + 2 * x3 + 3 * x5) * ((x1 + 2 * x3 + 3 * x5) * (x2 + x4)) = (x2 + x4) ^ 2 by field_simp ; linarith]
      rw [show (x3 + x5) / (x2 + 2 * x4 + 3 * x1) * ((x2 + 2 * x4 + 3 * x1) * (x3 + x5)) = (x3 + x5) ^ 2 by field_simp ; linarith]
      rw [show (x4 + x1) / (x3 + 2 * x5 + 3 * x2) * ((x3 + 2 * x5 + 3 * x2) * (x4 + x1)) = (x4 + x1) ^ 2 by field_simp ; linarith]
      rw [show (x5 + x2) / (x4 + 2 * x1 + 3 * x3) * ((x4 + 2 * x1 + 3 * x3) * (x5 + x2)) = (x5 + x2) ^ 2 by field_simp ; linarith]
      field_simp
      linarith
    -- Calculate the sum of f(i)^2, which equals our original function
    have h2 : ∑ i ∈ Finset.range 5, f i ^ 2 = (x1 + x3) / (x5 + 2 * x2 + 3 * x4) + (x2 + x4) / (x1 + 2 * x3 + 3 * x5) + (x3 + x5) / (x2 + 2 * x4 + 3 * x1) + (x4 + x1) / (x3 + 2 * x5 + 3 * x2) + (x5 + x2) / (x4 + 2 * x1 + 3 * x3):= by
      simp [Finset.sum_range_succ, hf]
      field_simp
    -- Calculate the sum of g(i)^2
    have h3 : ∑ i ∈ Finset.range 5, g i ^ 2 = (x5 + 2 * x2 + 3 * x4) * (x1 + x3) + (x1 + 2 * x3 + 3 * x5) * (x2 + x4) + (x2 + 2 * x4 + 3 * x1) * (x3 + x5) + (x3 + 2 * x5 + 3 * x2) * (x4 + x1) + (x4 + 2 * x1 + 3 * x3) * (x5 + x2):= by
      simp [Finset.sum_range_succ, hg]
      field_simp
      ring_nf
      field_simp
      ring_nf
    -- Prove that the sum of g(i)^2 is positive
    have h4 : ∑ i ∈ Finset.range 5, g i ^ 2 > 0:= by
      rw [h3]
      positivity
    -- Rearrange the Cauchy-Schwarz inequality
    replace h : (∑ i ∈ Finset.range 5, f i * g i) ^ 2 / (∑ i ∈ Finset.range 5, g i ^ 2) ≤ (∑ i ∈ Finset.range 5, f i ^ 2):= by exact (div_le_iff₀ h4).mpr h
    rw [h1, h2, h3] at h
    clear h1 h2 h3 h4
    -- Simplify the goal to show that the ratio is at least 5/3
    suffices (2 * (x1 + x2 + x3 + x4 + x5)) ^ 2 / ((x5 + 2 * x2 + 3 * x4) * (x1 + x3) + (x1 + 2 * x3 + 3 * x5) * (x2 + x4) + (x2 + 2 * x4 + 3 * x1) * (x3 + x5) + (x3 + 2 * x5 + 3 * x2) * (x4 + x1) + (x4 + 2 * x1 + 3 * x3) * (x5 + x2)) ≥ 5 / 3 by linarith
    clear h hf hg f g
    -- Prove that the denominator is positive
    have h : (x5 + 2 * x2 + 3 * x4) * (x1 + x3) + (x1 + 2 * x3 + 3 * x5) * (x2 + x4) + (x2 + 2 * x4 + 3 * x1) * (x3 + x5) +
    (x3 + 2 * x5 + 3 * x2) * (x4 + x1) + (x4 + 2 * x1 + 3 * x3) * (x5 + x2) > 0:= by positivity
    -- Further simplify the goal
    suffices (2 * (x1 + x2 + x3 + x4 + x5)) ^ 2 ≥ ((x5 + 2 * x2 + 3 * x4) * (x1 + x3) + (x1 + 2 * x3 + 3 * x5) * (x2 + x4) + (x2 + 2 * x4 + 3 * x1) * (x3 + x5) + (x3 + 2 * x5 + 3 * x2) * (x4 + x1) + (x4 + 2 * x1 + 3 * x3) * (x5 + x2)) * (5 / 3) by exact (le_div_iff₀' h).mpr this
    clear h
    -- Use a key inequality about squared differences
    have h : ∀ a b c : ℝ, 2 * (a - b) ^ 2 + 2 * (b - c) ^ 2 ≥ (a - c) ^ 2:= by
      intro a b c
      linarith only [sq_nonneg (a + c - 2 * b)]
    -- Apply the inequality to consecutive pairs of variables
    have h1:= h x1 x2 x3
    have h2:= h x2 x3 x4
    have h3:= h x3 x4 x5
    have h4:= h x4 x5 x1
    have h5:= h x5 x1 x2
    -- Complete the proof using linear arithmetic
    linarith
