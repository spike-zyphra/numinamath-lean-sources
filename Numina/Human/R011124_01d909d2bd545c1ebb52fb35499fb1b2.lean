import Mathlib

-- Open namespaces and scopes for easier writing 
open scoped Topology BigOperators Nat -- Using Topology/Filter, Summation notation, Nat literals
open Real Filter -- Using Real and Filter namespaces

/-
Evaluate $\sum_{i=1}^{\infty} \frac{(i+1)(i+2)(i+3)}{2^i}$.
-/
theorem algebra_610910 : ∑' (i : ℕ), ↑((i+1)*(i+2)*(i+3) : ℝ) / (2^i) = 96 := by
  -- Define x = 1/2
  let x : ℝ := (1 : ℝ) / 2
  -- Prove |x| < 1
  have hx_norm : ‖x‖ < 1 := by
    rw [norm_eq_abs, abs_eq_self.2 (by norm_num)] -- |1/2| = 1/2 since 1/2 >= 0
    norm_num -- Prove 1/2 < 1
  -- Rewrite the series term as a polynomial multiplied by x^i
  have heq : ∀ i : ℕ, ↑((i+1)*(i+2)*(i+3)) / (2^i) = ↑((i+1)*(i+2)*(i+3)) * x^i := by
    intro i
    simp [x, div_eq_mul_inv, ← one_div_pow] -- Simplify using definitions and power rules
  -- Rewrite the summation goal using x
  suffices ∑' i : ℕ, ↑((i+1)*(i+2)*(i+3)) * x^i = 96 by
    -- Use tsum_congr to apply the term equality
    rw [← this] -- Rewrite the goal using the backwards arrow (←) and the lemma `this`
    apply tsum_congr -- Apply congruence theorem for infinite sums
    norm_cast
    -- Provide the proof that terms are equal
    intro b
    rw [← heq b] 
    simp
  -- Rewrite the polynomial (i+1)*(i+2)*(i+3) using binomial coefficients
  -- We know (i+1)*(i+2)*(i+3) = 6 * Nat.descFactorial (i+3) 3 / Nat.factorial 3 = 6 * choose(i+3, 3)
  have poly_eq_binom : ∀ (i : ℕ), ↑((i+1)*(i+2)*(i+3)) = (6 : ℝ) * ↑((i+3).choose 3) := by
    intro i
    -- Prove (i+1)*(i+2)*(i+3) = (i+3).descFactorial 3
    have h_poly_eq : (i+1)*(i+2)*(i+3) = (i+3).descFactorial 3 := by
      -- Use the ring tactic to prove polynomial equality
      rw [Nat.descFactorial_eq_prod_range] -- descFactorial k n = product (k-j) for j in range n
      -- Expand Nat.descFactorial 3 definition: (i+3)*(i+3-1)*(i+3-2)
      simp only [Finset.prod_range_succ, Finset.range_one, Finset.prod_singleton, Finset.prod_empty, mul_one]
      norm_num -- Normalize numerical expressions inside the product
      rw [show i + 3 - 2 = i + 1 by omega] -- Simplify index using omega
      ring -- Prove the polynomial equality (i+1)*(i+2)*(i+3) = (i+3)*(i+2)*(i+1)

    -- Use the definition of binomial coefficient: choose k n = descFactorial k n / n!
    rw [Nat.choose_eq_descFactorial_div_factorial]
    -- Need to prove n! divides descFactorial k n to use cast_div
    have h_dvd : Nat.factorial 3 ∣ (i+3).descFactorial 3 := Nat.factorial_dvd_descFactorial (i + 3) 3
    -- Use cast_div and substitute polynomial equality, 3! = 6, and simplify
    rw [Nat.cast_div h_dvd (by aesop), h_poly_eq, show Nat.factorial 3 = 6 by rfl, Nat.cast_ofNat, mul_div, mul_comm]
    simp -- General simplification after rewrites

  -- Replace the polynomial in the summation goal with the binomial coefficient form
  suffices ∑' i : ℕ, (6 : ℝ) • (↑((i+3).choose 3) * x^i) = 96 by
    rw [← this] -- Rewrite goal using the lemma `this`
    apply tsum_congr -- Apply sum congruence
    intro i
    rw [poly_eq_binom i, mul_assoc, smul_eq_mul] -- Apply equivalence and adjust multiplication order

  -- Factor the constant 6 out of the summation
  suffices ∑' i : ℕ, ↑((i+3).choose 3) * x^i = 16 by
    -- Use tsum_const_smul'' to relate the sum with the constant factor (requires summability, inferred by hasSum)
    rw [show (96 : ℝ) = (6 : ℝ) • 16 by norm_num [smul_eq_mul], tsum_const_smul'']
    simp [this] -- Simplify using the lemma `this` (the sum equals 16)

  -- Use the known result from Mathlib: ∑' k, (k+n choose n) * x^k = (1-x)⁻¹ ^ (n+1)
  -- This is tsum_choose_mul_geometric_of_norm_lt_one n hx_norm
  -- Here n = 3
  convert tsum_choose_mul_geometric_of_norm_lt_one 3 hx_norm using 1
  -- The theorem gives the sum as ((1-x)⁻¹) ^ (3 + 1)
  -- Need to show this value equals 16 when x = 1/2
  -- The `convert` tactic leaves a goal to show the right-hand sides are equal
  -- `ring` tactic solves the final algebraic simplification: ((1 - 1/2)⁻¹)^4 = ( (1/2)⁻¹ )^4 = 2^4 = 16.
  ring