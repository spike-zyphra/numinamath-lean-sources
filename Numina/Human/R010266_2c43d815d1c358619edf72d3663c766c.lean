import Mathlib
/- The expression $\lfloor x\rfloor$ denotes the greatest integer less than or equal to $x$. Find the value of

$$
\left\lfloor\frac{2002!}{2001!+2000!+1999!+\cdots+1!}\right\rfloor .
$$ -/
theorem number_theory_611041 : ⌊(↑(Nat.factorial 2002) : ℝ) / (∑ i in Finset.range 2001, (↑(Nat.factorial (i + 1)) : ℝ))⌋ = 2000:= by
  -- We'll use the characterization of floor: ⌊x⌋ = n iff n ≤ x < n+1
  refine Int.floor_eq_iff.mpr ?_
  -- Set m = 2000 for cleaner notation
  set m:= 2000 with hm
  clear_value m
  -- Rewrite 2002 as m+2 and 2001 as m+1
  rw [show 2002 = m + 2 by omega]
  rw [show 2001 = m + 1 by omega]
  simp
  -- Prove that the sum of factorials is positive
  have h1 : ∑ i ∈ Finset.range (m + 1), (i + 1).factorial > 0:= by positivity
  rify at h1
  -- Prove that (n+2)! is greater than or equal to the sum of factorials from 1! to (n+1)!
  have h2 : ∀ n : ℕ, (n + 2).factorial ≥ ∑ i in Finset.range (n + 1), (i + 1).factorial:= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [show n + 1 + 2 = (n + 2) + 1 by omega]
      rw [Nat.factorial_succ]
      rw [show n + 1 + 1 = n + 2 by omega]
      simp at ih
      have g1 : (n + 1) * (n + 2).factorial > 0:= by positivity
      linarith
  constructor
  -- First part: Prove that 2000 ≤ 2002!/(sum of factorials)
  .
    suffices 2000 * ∑ i ∈ Finset.range (m + 1), ↑(i + 1).factorial ≤ (↑(m + 2).factorial : ℝ) by exact (le_div_iff₀ h1).mpr this
    rw [Finset.sum_range_succ]
    rw [show m = m - 1 + 1 by omega]
    rw [Finset.sum_range_succ]
    specialize h2 (m - 2)
    rw [show m - 2 + 2 = m by omega] at h2
    rw [show m - 1 + 1 = m by omega]
    rw [show m - 2 + 1 = m - 1 by omega] at h2
    suffices 2000 * (∑ x ∈ Finset.range (m - 1), (x + 1).factorial + m.factorial + (m + 1).factorial) ≤ (m + 2).factorial by rify at this ; exact this
    rw [show (m + 2).factorial = (m + 2) * (m + 1) * m.factorial by rw [Nat.factorial_succ] ; rw [Nat.factorial_succ] ; ring]
    rw [Nat.factorial_succ]
    suffices 2000 * (2 * m.factorial + (m + 1) * m.factorial) ≤ (m + 2) * (m + 1) * m.factorial by linarith
    rw [show m + 1 = 2001 by omega, show m + 2 = 2002 by omega]
    have g1 : m.factorial > 0:= by positivity
    linarith
  -- Second part: Prove that 2002!/(sum of factorials) < 2001
  .
    suffices (↑(m + 2).factorial : ℝ) < (2000 + 1) * (∑ i ∈ Finset.range (m + 1), ↑(i + 1).factorial) by exact (div_lt_iff₀ h1).mpr this
    rw [Finset.sum_range_succ]
    rw [show m = m - 1 + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [show m - 1 + 1 = m by omega]
    suffices (m + 2).factorial < (2000 + 1) * (∑ x ∈ Finset.range (m - 1), (x + 1).factorial + m.factorial + (m + 1).factorial) by rify at this ; exact this
    have h3 : ∑ x ∈ Finset.range (m - 1), (x + 1).factorial > 0:= by positivity
    suffices (m + 2).factorial ≤ (2000 + 1) * (m.factorial + (m + 1).factorial) by linarith
    clear h1 h2 h3
    rw [Nat.factorial_succ]
    rw [Nat.factorial_succ]
    rw [show m + 1 + 1 = 2002 by omega, show m + 1 = 2001 by omega]
    linarith
