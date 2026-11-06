import Mathlib
/- For an integer $n \geq 0$, let $f(n)$ be the smallest possible value of $|x+y|$, where $x$ and $y$ are integers such that $3 x-2 y=n$. Evaluate $f(0)+f(1)+f(2)+\cdots+f(2013)$. -/
theorem number_theory_609200 (f : ℕ → ℤ) (hn : ∀ n : ℕ, IsLeast {a : ℤ | ∃ x y : ℤ, (3 * x - 2 * y = n ∧ a = |x + y|)} (f n)) : ∑ i in Finset.range 2014, f i = 2416:= by
  -- Prove that f(5k) = 0 for any natural number k
  have h1 : ∀ k : ℕ, f (5 * k) = 0:= by
    intro k
    specialize hn (5 * k)
    suffices IsLeast {a : ℤ | ∃ x y : ℤ, 3 * x - 2 * y = ↑(5 * k) ∧ a = |x + y|} 0 by exact IsLeast.unique hn this
    constructor
    .
      simp
      -- Use x = k, y = -k as a witness that achieves |x + y| = 0
      use k, (-k)
      simp
      linarith
    .
      simp [lowerBounds]
      -- Show that 0 is indeed the minimum by using positivity of absolute values
      intro a x y _ ha
      subst a
      positivity
  -- Prove that f(5k+1) = 2 for any natural number k
  have h2 : ∀ k : ℕ, f (5 * k + 1) = 2:= by
    intro k
    specialize hn (5 * k + 1)
    suffices IsLeast {a : ℤ | ∃ x y : ℤ, 3 * x - 2 * y = ↑(5 * k + 1) ∧ a = |x + y|} 2 by exact IsLeast.unique hn this
    constructor
    .
      simp
      -- Use x = k+1, y = -k+1 as a witness that achieves |x + y| = 2
      use (k + 1), (-k + 1)
      constructor
      .
        linarith
      .
        ring_nf
        norm_num
    .
      simp [lowerBounds]
      -- Show that any solution must have |x + y| ≥ 2
      intro a x y h ha
      subst a
      replace h : 3 * (x + y) = 5 * (k + y) + 1:= by linarith
      set a:= k + y
      clear_value a
      have ha : a ≥ 1 ∨ a ≤ -2:= by omega
      suffices x + y ≤ -2 ∨ x + y ≥ 2 by exact le_abs'.mpr this
      rcases ha with ha | ha
      .
        right
        linarith
      .
        left
        linarith
  -- Prove that f(5k+2) = 1 for any natural number k
  have h3 : ∀ k : ℕ, f (5 * k + 2) = 1:= by
    intro k
    specialize hn (5 * k + 2)
    suffices IsLeast {a : ℤ | ∃ x y : ℤ, 3 * x - 2 * y = ↑(5 * k + 2) ∧ a = |x + y|} 1 by exact IsLeast.unique hn this
    constructor
    .
      simp
      -- Use x = k, y = -k-1 as a witness that achieves |x + y| = 1
      use k, (-k - 1)
      constructor
      .
        linarith
      .
        ring_nf
        norm_num
    .
      simp [lowerBounds]
      -- Show that any solution must have |x + y| ≥ 1
      intro a x y h ha
      subst a
      replace h : 3 * (x + y) = 5 * (k + y) + 2:= by linarith
      set a:= k + y
      clear_value a
      suffices x + y ≤ -1 ∨ x + y ≥ 1 by exact le_abs'.mpr this
      by_cases ha : a ≥ 0
      .
        right
        linarith
      .
        simp at ha
        left
        linarith
  -- Prove that f(5k+3) = 1 for any natural number k
  have h4 : ∀ k : ℕ, f (5 * k + 3) = 1:= by
    intro k
    specialize hn (5 * k + 3)
    suffices IsLeast {a : ℤ | ∃ x y : ℤ, 3 * x - 2 * y = ↑(5 * k + 3) ∧ a = |x + y|} 1 by exact IsLeast.unique hn this
    constructor
    .
      simp
      -- Use x = k+1, y = -k as a witness that achieves |x + y| = 1
      use (k + 1), (-k)
      constructor
      .
        linarith
      .
        ring_nf
        norm_num
    .
      simp [lowerBounds]
      -- Show that any solution must have |x + y| ≥ 1
      intro a x y h ha
      subst a
      replace h : 3 * (x + y) = 5 * (k + y) + 3:= by linarith
      set a:= k + y
      clear_value a
      suffices x + y ≤ -1 ∨ x + y ≥ 1 by exact le_abs'.mpr this
      replace ha : a < -1 ∨ a > -1:= by omega
      rcases ha with ha | ha
      .
        left
        linarith
      .
        right
        linarith
  -- Prove that f(5k+4) = 2 for any natural number k
  have h5 : ∀ k : ℕ, f (5 * k + 4) = 2:= by
    intro k
    specialize hn (5 * k + 4)
    suffices IsLeast {a : ℤ | ∃ x y : ℤ, 3 * x - 2 * y = ↑(5 * k + 4) ∧ a = |x + y|} 2 by exact IsLeast.unique hn this
    constructor
    .
      simp
      -- Use x = k, y = -k-2 as a witness that achieves |x + y| = 2
      use k, (-k - 2)
      constructor
      .
        linarith
      .
        ring_nf
        norm_num
    .
      simp [lowerBounds]
      -- Show that any solution must have |x + y| ≥ 2
      intro a x y h ha
      subst a
      replace h : 3 * (x + y) = 5 * (k + y) + 4:= by linarith
      set a:= k + y
      clear_value a
      suffices x + y ≤ -2 ∨ x + y ≥ 2 by exact le_abs'.mpr this
      replace ha : a < -1 ∨ a > -1:= by omega
      rcases ha with ha | ha
      .
        left
        linarith
      .
        right
        linarith
  -- Prove the sum formula: for any n, the sum of f(i) for i from 0 to 5n+3 equals 6n+4
  -- This uses the periodic pattern: f(5k)=0, f(5k+1)=2, f(5k+2)=1, f(5k+3)=1, f(5k+4)=2
  have h6 : ∀ n : ℕ, ∑ i in Finset.range (5 * n + 4), f i = 6 * n + 4:= by
    intro n
    induction n with
    | zero =>
      -- Base case: verify the formula for n = 0
      simp [Finset.sum_range_succ]
      rw [h1 0, h2 0, h3 0, h4 0]
      simp
    | succ n hn =>
      -- Inductive step: extend the sum by one complete period (5 terms)
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [show 5 * (n + 1) = 5 * n + 5 by ring]
      rw [Finset.sum_range_succ]
      rw [hn]
      rw [h5 n]
      rw [show 5 * n + 5 = 5 * (n + 1) by ring]
      rw [h1 (n + 1), h2 (n + 1), h3 (n + 1), h4 (n + 1)]
      simp
      linarith
  -- Apply the formula with n = 402 to get the final answer
  -- Since 2014 = 5 * 402 + 4, we have ∑ i in range 2014 = ∑ i in range (5 * 402 + 4)
  rw [h6 402]
  simp
