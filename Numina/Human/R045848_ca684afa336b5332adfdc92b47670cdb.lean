import Mathlib

/- 12. Let $n$ be a positive integer, when $n>100$, the first two digits of the decimal part of $\sqrt{n^{2}+3 n+1}$ are -/
theorem number_theory_243628 (n : ℕ) (hn : n > 100) :
    (⌊(√(n ^ 2 + 3 * n + 1)) * 100⌋) % 100 = 49 := by
  -- we'll express the square root with n + 1, so first show relation to it
  -- the main crux move is that n^2 + 3n + 1 > n^2 + 2n + 1 = (n+1)^2
  have : n + 1 < √(n^2 + 3*n + 1) := by calc
    n + 1 = √((n+1)^2) := by
      rw [Real.sqrt_sq]
      positivity
    _ < √(n^2 + 3*n + 1) := by
      gcongr
      norm_cast
      linarith
  -- also show some positivities
  have : 0 < √(n ^ 2 + 3 * n + 1) + n + 1 := by positivity
  have : 0 < √(n ^ 2 + 3 * n + 1) - n - 1 := by linarith
  -- now show following equality as the rhs can be used for bounding
  have h1 : 1 / (√(n^2 + 3*n + 1) - n - 1) - 2 = √(1/n^2 + 3/n + 1) - 1 + 1/n := by calc
    1 / (√(n^2 + 3*n + 1) - n - 1) - 2 = (√(n^2 + 3*n + 1) + n + 1) / ((√(n^2 + 3*n + 1) - n - 1) * ((√(n^2 + 3*n + 1) + n + 1)) ) - 2 := by
      congr 1
      field_simp
    _ = (√(n^2 + 3*n + 1) + n + 1) / n - 2 := by
      congr
      ring_nf
      rw [Real.sq_sqrt (by positivity)]
      ring
    _ = √((n^2 + 3 * n + 1) / n^2) + 1 + 1/n - 2 := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
      field_simp
    _ =  √(1/n^2 + 3/n + 1) - 1 + 1/n := by
      have : (1:ℝ)/n^2 + 3/n + 1 = (n^2 + 3*n + 1) / n^2 := by
        field_simp
        ring
      rw [this]
      ring
  -- show that the rhs is positive
  have h2 : 0 < 1 / (√(n^2 + 3*n + 1) - n - 1) - 2 := by calc
    (0:ℝ) < (1 + 1/n) - (1 - 1/n) := by
      ring_nf
      positivity
    _ = √((1 + 1/n)^2) - (1 - 1/n) := by
      rw [Real.sqrt_sq (by positivity)]
    _ < √(1/n^2 + 3/n + 1) - (1 - 1/n) := by
      gcongr
      have : (0:ℝ) < 1/n := by positivity
      ring_nf at this ⊢
      linarith
    _ = 1 / (√(n^2 + 3*n + 1) - n - 1) - 2 := by
      rw [h1]
      ring
  -- show rhs is less than 2/49
  have h3 : 1 / (√(n^2 + 3*n + 1) - n - 1) - 2 < 2 / 49 := by calc
    _ = √(1/n^2 + 3/n + 1) - 1 + 1/n := by rw [h1]
    _ < √(4/n^2 + 4/n + 1) - 1 + 1/n := by
      gcongr <;> norm_num
    _ = √((1 + 2/n)^2) - 1 + 1/n := by
      congr
      ring
    _ = 3 / n := by
      rw [Real.sqrt_sq (by positivity)]
      ring
    _ ≤ 3 / 101 := by
      gcongr
      norm_num
      omega
    _ < 2 / 49 := by norm_num
  -- now using the last two inequality to relate to √(n^2+3n+1)
  replace h2 : 1 / (1/2) < 1 / (√(n^2 + 3*n + 1) - n - 1) := by linarith
  replace h2 := lt_of_one_div_lt_one_div (by simp) h2
  replace h2 : 100 * √(n^2 + 3*n + 1) < 100 * (n + 1) + 50 := by linarith
  replace h3 : 1 / (√(n^2 + 3*n + 1) - n - 1) < 1/(49/100) := by linarith
  replace h3 := lt_of_one_div_lt_one_div (by positivity) h3
  replace h3 : 100 * (n + 1) + 49 ≤ 100 * √(n^2 + 3*n + 1) := by linarith
  -- from the facts, we can prove floor value
  have h4 : ⌊100 * √(n^2 + 3*n + 1)⌋ = 100 * (n + 1) + 49 := by
    refine Int.floor_eq_iff.mpr ?_
    and_intros
    . push_cast
      assumption
    . push_cast
      linarith
  -- now just use mod to get the value 49
  rw [mul_comm, h4]
  norm_cast
  rw [Nat.mul_add_mod]