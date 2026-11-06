import Mathlib
open Finset Polynomial
noncomputable section

-- Lemma: Prove $|xi - x₀| = 1$ for any $xi$ where $|P.eval xi| = 1$.
lemma abs_dist_one {P φ : Polynomial ℤ} {x₀ xi : ℤ} 
  (hφ : P = (X - C x₀) * φ) (h_xi : |P.eval xi| = 1) : |(xi - x₀ : ℤ)| = 1 := by
  -- Absolute value of $P$ at $xi$ is $1$.
  have h_xi_abs1 : |P.eval xi| = 1 := h_xi
  -- Evaluate $P$ at $xi$.
  have h_xi_eval : P.eval xi = (xi - x₀ : ℤ) * φ.eval xi := by
    rw [hφ]
    simp [eval_mul, eval_sub, eval_X, eval_C]
  -- Absolute value of product is $1$.
  have h_prod_abs : |(xi - x₀ : ℤ) * φ.eval xi| = 1 := by
    rw [h_xi_eval] at h_xi_abs1
    simpa using h_xi_abs1
  -- Split absolute value of product.
  have h_abs_split : |(xi - x₀ : ℤ)| * |(φ.eval xi : ℤ)| = 1 := by
    simpa [abs_mul] using h_prod_abs
  -- Prove $|xi - x₀| ≥ 1$ by contradiction.
  have h_abs_ge1 : |(xi - x₀ : ℤ)| ≥ 1 := by
    by_contra h
    rw [Int.not_le, Int.abs_lt_one_iff] at h
    have : P.eval xi = 0 := by
      rw [h_xi_eval, h]
      simp
    rw [this] at h_xi_abs1
    norm_num at h_xi_abs1
  -- Non-negativity of $|φ.eval xi|$.
  have h_phi_nonneg : |(φ.eval xi : ℤ)| ≥ 0 := abs_nonneg _
  -- Conclude $|xi - x₀| = 1$.
  have h_abs_eq1 : |(xi - x₀ : ℤ)| = 1 := by
    have h_prod_eq1 : |(xi - x₀ : ℤ)| * |(φ.eval xi : ℤ)| = 1 := h_abs_split
    have h_phi_abs_ge1 : |(φ.eval xi : ℤ)| ≥ 1 := by
      by_contra h_neg
      have : |(φ.eval xi : ℤ)| = 0 := by omega
      rw [this, mul_zero] at h_prod_eq1
      norm_num at h_prod_eq1
    nlinarith
  exact h_abs_eq1

/- $5.60 Prove: If for three different integer values of $x$, the absolute value of the value of an integer-coefficient polynomial in $x$ is 1, then this polynomial has no integer roots. -/
theorem algebra_277945 {P : Polynomial ℤ} (hP : ∃ x1 x2 x3 : ℤ, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧ |P.eval x1| = 1 ∧ |P.eval x2| = 1 ∧ |P.eval x3| = 1) :
    ¬∃ x : ℤ, P.eval x = 0 := by 
  -- Prove no integer root exists.
  have h_no_root : ¬∃ x : ℤ, P.eval x = 0 := by
    intro h
    obtain ⟨x₀, hx₀⟩ := h
    obtain ⟨x1, x2, x3, hx1x2, hx2x3, hx3x1, hx1, hx2, hx3⟩ := hP
    -- Show $(X - C x₀)$ divides $P$
    have h_div_x0 : (X - C (x₀ : ℤ)) ∣ P := by
      apply Polynomial.dvd_iff_isRoot.mpr
      simp [hx₀]
    obtain ⟨φ, hφ⟩ := h_div_x0
    -- Factorize $P$.
    have h_factor : P = (X - C (x₀ : ℤ)) * φ := by
      rw [hφ]
    -- Prove $|x1 - x₀| = 1$ and $|x2 - x₀| = 1$ and $|x3 - x₀| = 1$ by using the lemma.
    have h_x1_dist : |(x1 - x₀ : ℤ)| = 1 := abs_dist_one h_factor hx1
    have h_x2_dist : |(x2 - x₀ : ℤ)| = 1 := abs_dist_one h_factor hx2
    have h_x3_dist : |(x3 - x₀ : ℤ)| = 1 := abs_dist_one h_factor hx3
    -- Show at least two of $x1$, $x2$, $x3$ are equal.
    have h_equal_pair : x1 = x2 ∨ x1 = x3 ∨ x2 = x3 := by
      have h_x1_abs1 : |(x1 - x₀ : ℤ)| = 1 := h_x1_dist
      have h_x2_abs1 : |(x2 - x₀ : ℤ)| = 1 := h_x2_dist
      have h_x3_abs1 : |(x3 - x₀ : ℤ)| = 1 := h_x3_dist
      -- Possible values for $x1 - x₀$.
      have h_x1_values : x1 - x₀ = 1 ∨ x1 - x₀ = -1 := by
        rw [abs_eq] at h_x1_abs1
        exact h_x1_abs1
        linarith
      -- Possible values for $x2 - x₀$.
      have h_x2_values : x2 - x₀ = 1 ∨ x2 - x₀ = -1 := by
        rw [abs_eq] at h_x2_abs1
        exact h_x2_abs1
        linarith
      -- Possible values for $x3 - x₀$.
      have h_x3_values : x3 - x₀ = 1 ∨ x3 - x₀ = -1 := by
        rw [abs_eq] at h_x3_abs1
        exact h_x3_abs1
        linarith
      -- Case analysis on possible values.
      have h_pair_eq : x1 = x2 ∨ x1 = x3 ∨ x2 = x3 := by
        cases' h_x1_values with h1 h1
        · cases' h_x2_values with h2 h2
          · exact Or.inl (by linarith)
          · cases' h_x3_values with h3 h3
            · exact Or.inr (Or.inl (by linarith))
            · exact Or.inr (Or.inr (by linarith))
        · cases' h_x2_values with h2 h2
          · cases' h_x3_values with h3 h3
            · exact Or.inr (Or.inr (by linarith))
            · exact Or.inr (Or.inl (by linarith))
          · exact Or.inl (by linarith)
      exact h_pair_eq
    -- Derive contradiction.
    have h_contradict : False := by
      have h₈₁ : x1 ≠ x2 := hx1x2
      have h₈₂ : x2 ≠ x3 := hx2x3
      have h₈₃ : x3 ≠ x1 := hx3x1
      have h₈₄ : x1 = x2 ∨ x1 = x3 ∨ x2 = x3 := h_equal_pair
      tauto
    exact h_contradict
  exact h_no_root