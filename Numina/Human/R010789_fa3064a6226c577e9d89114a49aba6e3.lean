import Mathlib

/- 1.6. $7^{* *}$ Let $Q_{1}=\{x \in \mathbf{Q} \mid x \geqslant 1\}$. Suppose the function $f: Q_{1} \rightarrow R$ satisfies the inequality for any $x, y \in Q_{1}$:

$$

|f(x+y)-f(x)-f(y)|<\varepsilon,

$$


where $\varepsilon$ is some positive real number. Prove: There exists $q \in \mathbf{R}$, such that for any $x \in Q_{1}$, we have $\left|\frac{f(x)}{x}-q\right|<2 \varepsilon$. -/
theorem algebra_227311
  (Q : Set ℚ)
  (hQ : Q = {x | 1 ≤ x})
  (f : ℚ → ℝ)
  (ε : ℝ)
  (hε : ε > 0)
  (h : ∀ x ∈ Q, ∀ y ∈ Q, |f (x + y) - f x - f y| < ε) :
  ∃ q : ℝ, ∀ x ∈ Q, |(f x) / x - q| < 2 * ε := by
  -- first we prove a result that (n+1)*f(x) - n * ε ≤ f((n+1)*x) ≤ (n+1)*f(x) + n * ε via induction
  have h_ineq (n : ℕ) (x : ℚ) (hx : x ∈ Q) : (n + 1) * f x - n * ε ≤ f ((n + 1) * x) ∧ f ((n + 1) * x) ≤ (n + 1) * f x + n * ε := by
    induction' n with m hm
    . simp
    . replace h := by
        refine h x hx ((m + 1) * x) ?_
        rw [hQ]
        calc
          1 ≤ x := by rw [hQ] at hx; exact hx
          _ ≤ (m + 1) * x := by
            apply le_mul_of_one_le_left
            . rw [hQ] at hx
              simp at hx
              linarith
            . linarith
      replace h := abs_lt.mp h
      rw [show x + (m + 1) * x = (m + 2) * x by ring] at h
      and_intros
      . have : (m + 2) * f x - (m + 1) * ε ≤ f ((m + 2) * x) := by linarith only [h.left, hm.left]
        exact_mod_cast this
      . have : f ((m + 2) * x) ≤ (m + 2) * f x + (m + 1) * ε := by linarith only [h.right, hm.right]
        exact_mod_cast this
  -- apply the result on x = 1
  have h1 (n : ℕ) := h_ineq n 1 (by rw [hQ]; norm_num)
  simp only [mul_one] at h1
  -- we will prove that a witness for q is f(1)
  use (f 1)
  rintro x hx
  -- first prove x must be of form m / (n + 1) by using x.num.natAbs and x.den-1
  have hx' : ∃ (m n : ℕ), n + 1 ≤ m ∧ x = (m / (n + 1) : ℚ) := by
    use x.num.natAbs, x.den - 1
    rw [hQ] at hx
    have : x.den > 0 := by exact Rat.den_pos x
    and_intros
    . rw [show x.den - 1 + 1 = x.den by omega]
      have := calc
        x.den ≤ x.num := by
          rw [← Rat.num_div_den x] at hx
          simp at hx
          have := one_le_div_iff.mp hx
          norm_cast at this
          simp at this
          exact_mod_cast this.right
        _ ≤ x.num.natAbs := by exact Int.le_natAbs
      exact_mod_cast this
    . norm_cast
      rw [show x.den - 1 + 1 = x.den by omega]
      nth_rw 1 [← Rat.num_div_den x]
      congr
      simp at hx
      exact Int.eq_natAbs_of_zero_le (Rat.num_nonneg.mpr (by linarith))
  -- replace instances of x by m/(n+1)
  obtain ⟨m, n, hmn', hx'⟩ := hx'
  -- apply h_ineq on x and n for natural number
  replace h_ineq := h_ineq n x hx
  -- we will prove the upper bound (m-1+n)/m * ε as this is less than 2
  suffices  |f x / x - f 1| ≤ (↑(m-1) + n)/m * ε by
    have : (↑(m - 1) + ↑n) / m * ε < 2 * ε := by
      gcongr
      rw [add_div, show (2:ℝ) = 1 + 1 by norm_num]
      gcongr
      . refine Bound.div_lt_one_of_pos_of_lt ?_ ?_ <;> norm_cast
        . linarith
        . omega
      . refine Bound.div_lt_one_of_pos_of_lt ?_ ?_ <;> norm_cast
        . linarith
    linarith
  rw [hx'] at h_ineq ⊢
  rw [show (n+1) * (m / (n+1) : ℚ) = m by field_simp] at h_ineq
  -- apply h1 to the natural number m - 1
  replace h1 := h1 (m - 1)
  have : 0 < m := by linarith
  norm_cast at h1
  rw [show m - 1 + 1 = m by omega] at h1
  -- we will prove -a ≤ b ≤ a for |b| < a
  apply abs_le.mpr
  and_intros
  -- in both cases we merge h1 and h_ineq, then divide by m
  . have : - ↑(m-1) * ε - n * ε ≤ (n+1) * f (m / (n+1)) - m * f 1 := by linarith only [h1.left, h_ineq.right]
    have : (- ↑(m-1) * ε - n * ε)/m ≤ ((n + 1) * f (m / (n + 1)) - m * f 1)/m := by gcongr
    convert this using 1
    . ring
    . field_simp
      ring
  . have : (n+1) * f (m / (n+1)) - m * f 1 ≤ ↑(m-1) * ε + n * ε := by linarith only [h1.right, h_ineq.left]
    have : ((n+1) * f (m / (n+1)) - m * f 1)/m ≤ (↑(m-1) * ε + n * ε)/m := by gcongr
    convert this using 1
    . field_simp
      ring
    . ring