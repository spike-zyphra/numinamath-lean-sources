import Mathlib

open Polynomial

/-
09.2. On a faded piece of paper it is possible, with some effort, to discern the following:
$$
\left(x^{2}+x+a\right)\left(x^{15}-\ldots\right)=x^{17}+x^{13}+x^{5}-90 x^{4}+x-90
$$
Some parts have got lost, partly the constant term of the first factor of the left side, partly the main part of the other factor. It would be possible to restore the polynomial forming the other factor, but we restrict ourselves to asking the question: What is the value of the constant term a? We assume that all polynomials in the statement above have only integer coefficients.
 -/

-- lemma that a ∣ 90, 184 means a ∣ 2, their gcd
lemma l_gcd  {a b c : ℤ} (h1 : a * b = -90) (h2 : a * c = -184) : a ∣ 2 := by
  replace h1 : a ∣ -90 := by simp [← h1]
  replace h2 : a ∣ -184 := by simp [← h2]
  have h3 := Int.dvd_gcd h1 h2
  norm_num at h3
  assumption

-- if a ∣ b then a is from b's natural divisors or -a is from b's natural divisors
lemma l_divisor {a b : ℤ} (h : a ∣ b) (hb : b ≠ 0) : a ∈ b.natAbs.divisors.map ⟨(↑), Nat.cast_injective⟩ ∨
    -a ∈ b.natAbs.divisors.map ⟨(↑), Nat.cast_injective⟩ := by
  simp [hb]
  obtain ha | ha := le_total 0 a
  . left
    use a.natAbs
    simp [ha, h]
  . right
    use a.natAbs
    simp [ha, h]

theorem algebra_111373 (a : ℤ) (Q : ℤ[X]) (h : (X^2 + X + C a) * Q = (X^17 + X^13 + X^5 - 90 * X^4 + X - 90))
    : a = 2 := by
  -- evaluate at x = 0
  have h0 := congr_arg (fun f => f.eval 0) h
  simp [eval_mul, eval_add, eval_pow, eval_X, eval_C] at h0
  -- evaluate at x = 1
  have h1 := congr_arg (fun f => f.eval 1) h
  simp [eval_add, eval_mul, eval_pow, eval_X, eval_C] at h1
  -- evaluate at x = -1
  have h2 := congr_arg (fun f => f.eval (-1)) h
  simp [eval_add, eval_mul, eval_pow, eval_X, eval_C] at h2
  -- evaluate at x = 2
  have h3 := congr_arg (fun f => f.eval 2) h
  norm_num [eval_add, eval_mul, eval_pow, eval_X, eval_C] at h3
  -- deriv divisibility
  have h4 : a ∣ -90 := by
    use Q.eval 0
    all_goals linarith
  -- deriv divisibility
  have h5 : a ∣ -184 := by
    use Q.eval (-1)
    all_goals linarith
  -- deriv divisibility
  have h6 : a ∣ 2 := by
    exact Int.dvd_gcd h4 h5
  -- solve by case divisibility by 2
  have h7 : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2 := by
    have h89 : a ∣ 2 := h6
    have : a ≤ 2 := by
      apply Int.le_of_dvd (by norm_num) h89
    have : a ≥ -2 := by
      have h9 : (-a) ∣ 2 := by
        exact Int.neg_dvd.2 h89
      have h10 : -a ≤ 2 := by
        apply Int.le_of_dvd (by norm_num) h9
      omega
    interval_cases a <;> tauto
  rcases h7 with (r | r | r | r)
  · -- Assume a = 1
    rw [show a = 1 by linarith [r] ] at h1
    omega
  · -- Assume a = -1
    rw [show a = -1 by linarith [r] ] at h1 h3
    omega
  · -- Assume a = 2
    linarith
  · -- Assume a = -2
    rw [show a = -2 by linarith [r] ] at h0 h1
    all_goals linarith