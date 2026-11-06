import Mathlib

open Real Set
open scoped BigOperators

/- Subject 2. Find the real numbers $\mathrm{x}$ and $\mathrm{y}$ for which we have


$$

\sqrt{4 x^{2}-12 x+25}+\sqrt{4 x^{2}+12 x y+9 y^{2}+64} \leq 12

$$
 -/
theorem inequalities_110574 (x y : ℝ) : sqrt (4 * x ^ 2 - 12 * x + 25) + sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) ≤ 12 ↔ (x = 3 / 2 ∧ y = -1) := by
  -- Establish the first inequality
  have f1' : sqrt (4 * x ^ 2 - 12 * x + 25) ≥ 4 := by
    calc
      sqrt (4 * x ^ 2 - 12 * x + 25) = sqrt ((2*x - 3)^2 + 16) := by ring_nf
      _ ≥ sqrt (0 + 16) := sqrt_le_sqrt (by linarith [sq_nonneg (2*x - 3)])
      _ = 4 := by rw [zero_add]; apply (sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr; norm_num
  -- Establish equality condition
  have f1 : sqrt (4 * x ^ 2 - 12 * x + 25) = 4 ↔ x = 3/2 := by
    constructor
    -- Prove x = 3/2 is the only solution
    · intro h
      rw [sqrt_eq_cases] at h
      rcases h with h | h
      · have : (2*x - 3)^2 = 0 := by ring; linarith
        rw [sq_eq_zero_iff] at this
        linarith
      -- Impossible case
      linarith
    -- Prove that x = 3/2 is a valid solution
    intro hx
    norm_num [hx]
    apply (sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr;
    norm_num
  -- Establish the second inequality and equality condition
  have f2' : sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) ≥ 8 := by
    calc
      sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) = sqrt ((2*x + 3*y)^2 + 64) := by ring_nf
      _ ≥ sqrt (0 + 64) := sqrt_le_sqrt (by linarith [sq_nonneg (2*x + 3*y)])
      _ = 8 := by rw [zero_add]; apply (sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr; norm_num
  have f2 : sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) = 8 ↔ 2*x + 3*y = 0 := by
    constructor
    -- Prove x = 3/2 is the only solution
    · intro h
      rw [sqrt_eq_cases] at h
      rcases h with h | h
      · have : (2*x + 3*y)^2 = 0 := by ring; linarith
        rw [sq_eq_zero_iff] at this
        linarith
      -- Impossible case
      linarith
    -- Prove that x = 3/2 is a valid solution
    intro hx
    apply (sqrt_eq_iff_eq_sq _ (by positivity)).mpr
    · rw [← sq_eq_zero_iff] at hx
      linarith
    have : 4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64 = (2*x + 3*y)^2 + 64 := by ring
    rw [this]
    positivity
  -- Combine the two inequalities and establish equality condition
  have f3' : sqrt (4 * x ^ 2 - 12 * x + 25) + sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) ≥ 12 := by linarith
  have f3 : sqrt (4 * x ^ 2 - 12 * x + 25) + sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) = 12 ↔ (x = 3/2 ∧ y = -1) := by
    -- For notational convenience
    let a := sqrt (4 * x ^ 2 - 12 * x + 25)
    let b := sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64)
    change a ≥ 4 at f1'
    change b ≥ 8 at f2'
    change a + b = 12 ↔ x = 3/2 ∧ y = -1
    constructor
    -- Prove that if equality holds, then x and y must be 3/2 and -1
    · intro h
      have fact1 : a = 4 ∧ b = 8 := by
        apply And.intro
        · linarith
        linarith
      have hx : x = 3/2 := f1.mp fact1.1
      have hy : y = -1 := by
        have : 2*x + 3*y = 0 := f2.mp fact1.2
        linarith
      exact ⟨hx, hy⟩
    -- Prove that (x, y) = (3/2, -1) works
    rintro ⟨hx, hy⟩
    have ha : a = 4 := f1.mpr hx
    have hb : b = 8 := by
      have : 2*x + 3*y = 0 := by linarith
      exact f2.mpr this
    linarith
  -- Now we've solved the bulk of the problem, the rest is just logic.
  constructor
  · intro h
    have : sqrt (4 * x ^ 2 - 12 * x + 25) + sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) = 12 := by linarith
    exact f3.mp this
  intro h
  have : sqrt (4 * x ^ 2 - 12 * x + 25) + sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) = 12 := f3.mpr h
  linarith