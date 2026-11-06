import Mathlib

/- 331. Prove that for $p>n$ and $a>b>0$

$$
\frac{a^{p}-b^{p}}{a^{p}+b^{p}}>\frac{a^{n}-b^{n}}{a^{n}+b^{n}}
$$ -/
theorem inequalities_277302 (p n : ℝ) (a b : ℝ) (ha : 0 < b) (hb : b < a)
    (hp : p > n) :
    (a ^ p - b ^ p) / (a ^ p + b ^ p) > (a ^ n - b ^ n) / (a ^ n + b ^ n) := by
  -- First, we prove that the denominator of the left side is positive
  have h2 : a ^ p + b ^ p > 0 := by
    apply add_pos
    · -- a^p > 0 since a > 0 and real power of positive is positive
      apply Real.rpow_pos_of_pos
      linarith
    · -- b^p > 0 since b > 0 and real power of positive is positive
      apply Real.rpow_pos_of_pos
      linarith
  -- Similarly, we prove that the denominator of the right side is positive
  have h3 : a ^ n + b ^ n > 0 := by
    apply add_pos
    · -- a^n > 0 since a > 0 and real power of positive is positive
      apply Real.rpow_pos_of_pos
      linarith
    · -- b^n > 0 since b > 0 and real power of positive is positive
      apply Real.rpow_pos_of_pos
      linarith
  -- The key insight: proving that a^p * b^n > a^n * b^p
  have h4 : a ^ p * b ^ n > a ^ n * b ^ p := by
    -- We first show that a^(p-n) > b^(p-n)
    have h5 : a ^ (p - n) > b ^ (p - n) := by
      have h10 : a ^ (p - n) > b ^ (p - n) := by
        -- Since a > b > 0 and p-n > 0, we have a^(p-n) > b^(p-n)
        apply Real.rpow_lt_rpow
        all_goals linarith
      linarith
    -- Now we prove that a^p * b^n - a^n * b^p > 0
    have h10 : a ^ p * b ^ n - (a ^ n * b ^ p) > 0 := by
      -- Algebraic manipulation to factor out the difference of powers
      have h11 : a ^ p * b ^ n - (a ^ n * b ^ p) = a ^ n * b ^ n * (a ^ (p - n) - b ^ (p - n)) := by
        -- Using the property that a^(n+m) = a^n * a^m
        have h12 : a ^ p = a ^ n * a ^ (p - n) := by
          rw [← Real.rpow_add (by linarith)]
          ring_nf
        -- Similarly for b
        have h13 : b ^ p = b ^ n * b ^ (p - n) := by
          rw [← Real.rpow_add (by linarith)]
          ring_nf
        rw [h12, h13]
        ring
      -- Substitute the factored form and prove positivity
      rw [h11]
      apply mul_pos
      apply mul_pos
      · -- a^n > 0
        apply Real.rpow_pos_of_pos
        linarith
      · -- b^n > 0
        apply Real.rpow_pos_of_pos
        linarith
      · linarith
    linarith
  -- Apply the division inequality lemma
  -- If denominators are positive and a/b < c/d, then (a-c)/(b-d) < a/b
  apply (div_lt_div_iff (by linarith) (by linarith)).mpr
  -- Use nonlinear arithmetic to complete the proof
  nlinarith [h4]
