import Mathlib
/- 8・148 Let $x_{0}=10^{9}, x_{n}=\frac{x_{n-1}^{2}+2}{2 x_{n-1}}, n=1,2,3, \cdots$ Prove: $0< x_ {36} -\sqrt {2} <10^{-9}$. -/
theorem algebra_602810 (x : ℕ → ℝ) (h1 : x 0 = 10 ^ 9) (h2 : ∀ n : ℕ, x (n + 1) = (x n ^ 2 + 2) / (2 * x n)) : 0 < x 36 - √2 ∧ x 36 - √2 < 10 ^ (-9 : ℝ):= by
  -- First prove that all terms in the sequence are greater than √2
  have h3 : ∀ n : ℕ, x n > √2:= by
    intro n
    induction n with
    | zero =>
      -- Base case: x_0 = 10^9 > √2
      have g1 : √2 ≤ √4:= by
        have g1 : (2 : ℝ) ≤ 4:= by norm_num
        exact Real.sqrt_le_sqrt g1
      rw [show √4 = √(2 ^ 2) by ring_nf] at g1
      field_simp at g1
      linarith
    | succ n ih =>
      -- Inductive step: if x_n > √2, then x_{n+1} > √2
      rw [h2 n]
      suffices (x n ^ 2 + 2) / (2 * x n) - √2 > 0 by linarith
      have g1 : √2 > 0:= by norm_num
      replace g1 : x n > 0:= by linarith
      rw [show (x n ^ 2 + 2) / (2 * x n) - √2 = (x n - √2) ^ 2 / (2 * x n) by ring_nf ; field_simp ; ring_nf]
      replace ih : x n - √2 > 0:= by linarith
      positivity
  -- Use the first part of the inequality (x_36 > √2)
  refine ⟨(by linarith only [h3 36]), ?_⟩
  -- Rewrite the recurrence relation in terms of (x_{n+1} - √2)
  replace h2 : ∀ n : ℕ, x (n + 1) - √2 = (x n - √2) ^ 2 / (2 * x n) := by
    intro n
    rw [h2 n]
    specialize h3 n
    have g1 : x n > 0:= by linarith [show √2 > 0 by norm_num]
    field_simp
    ring_nf
    field_simp
    ring_nf
  -- Show that the sequence converges to √2 with rate 1/2
  have h4 : ∀ n : ℕ, x (n + 1) - √2 < 1 / 2 * (x n - √2):= by
    intro n
    rw [h2 n]
    specialize h3 n
    have g1 : x n > 0:= by linarith [show √2 > 0 by norm_num]
    rw [show (x n - √2) ^ 2 / (2 * x n) = (x n - √2) / x n * (1 / 2 * (x n - √2)) by ring]
    have g2 : (x n - √2) / x n < 1:= by
      suffices x n - √2 < 1 * x n by exact (div_lt_iff₀ g1).mpr this
      linarith [show √2 > 0 by norm_num]
    have g3 : 1 / 2 * (x n - √2) > 0:= by
      replace h3 : x n - √2 > 0:= by linarith
      positivity
    exact mul_lt_of_lt_one_left g3 g2
  -- Establish upper bound: x_n - √2 ≤ (1/2)^n * (x_0 - √2)
  replace h4 : ∀ n : ℕ, x n - √2 ≤ (1 / 2) ^ n  * (x 0 - √2):= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      specialize h4 n
      rw [show ((1 : ℝ) / 2) ^ (n + 1) = (1 / 2) ^ n * (1 / 2) by ring_nf]
      linarith
  -- Show that x_30 - √2 < 1
  specialize h4 30
  replace h4 : x 30 - √2 < 1:= by
    have g1 : x 0 - √2 < x 0:= by linarith [show √2 > 0 by norm_num]
    linarith
  -- Establish a better bound for later terms using quadratic convergence
  replace h2 : ∀ n : ℕ, x (n + 1) - √2 < (x n - √2) ^ 2 / (2 * √2):= by
    intro n
    rw [h2 n]
    specialize h3 n
    have g1 : (x n - √2) ^ 2 > 0:= by
      replace h3 : x n - √2 > 0:= by linarith
      positivity
    have g2 : 2 * √2 > 0:= by positivity
    suffices 2 * x n > 2 * √2 by exact div_lt_div_of_pos_left g1 g2 this
    linarith
  -- Establish exponential bound for terms after x_30
  replace h2 : ∀ n : ℕ, x (n + 30) - √2 ≤ (1 / (2 * √2)) ^ (2 ^ n - 1) * (x 30 - √2):= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      specialize h2 (n + 30)
      rw [show n + 1 + 30 = (n + 30) + 1 by ring_nf]
      set t:= (1 / (2 * √2)) ^ (2 ^ n - 1) with ht
      clear_value t
      -- Show that the exponent doubles in each step
      have ht1 : t ^ 2 * (1 / (2 * √2)) = (1 / (2 * √2)) ^ (2 ^ (n + 1) - 1):= by
        subst t
        set s:= 1 / (2 * √2) with hs
        clear_value s
        rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by ring_nf]
        rw [show (s ^ (2 ^ n - 1)) ^ 2 = s ^ ((2 ^ n - 1) * 2) by exact Eq.symm (pow_mul s (2 ^ n - 1) 2)]
        have g1 : 2 ^ n > 0:= by positivity
        rw [show (2 ^ n - 1) * 2 = 2 ^ n + 2 ^ n - 2 by omega]
        rw [show 2 ^ n + 2 ^ n - 1 = 2 ^ n + 2 ^ n - 2 + 1 by omega]
        rw [show s ^ (2 ^ n + 2 ^ n - 2 + 1) = s ^ (2 ^ n + 2 ^ n - 2) * s by ring]
      rw [←ht1]
      clear ht1
      -- Use the quadratic convergence property
      have g:= h3 30
      specialize h3 (n + 30)
      replace h3 : x (n + 30) - √2 ≥ 0:= by linarith
      replace ih : (x (n + 30) - √2) ^ 2 ≤ (t * (x 30 - √2)) ^ 2:= by exact pow_le_pow_left h3 ih 2
      rw [show (t * (x 30 - √2)) ^ 2 = t ^ 2 * (x 30 - √2) ^ 2 by ring_nf] at ih
      -- Use the fact that (x_30 - √2)^2 ≤ x_30 - √2 since x_30 - √2 < 1
      have g1 : (x 30 - √2) ^ 2 ≤ x 30 - √2:= by
        replace h4 : x 30 - √2 ≤ 1:= by linarith
        replace g : x 30 - √2 ≥ 0:= by linarith
        exact sq_le g h4
      replace g1 : t ^ 2 * (x 30 - √2) ^ 2 ≤ t ^ 2 * (x 30 - √2):= by
        have g2 : t ^ 2 ≥ 0:= by positivity
        exact mul_le_mul_of_nonneg_left g1 g2
      rw [show (x (n + 30) - √2) ^ 2 / (2 * √2) = (x (n + 30) - √2) ^ 2 * (1 / (2 * √2)) by ring] at h2
      have g2 : 1 / (2 * √2) ≥ 0:= by positivity
      replace ih:= mul_le_mul_of_nonneg_left ih g2
      replace g1:= mul_le_mul_of_nonneg_left g1 g2
      linarith
  -- Apply the bound to n = 6 to get x_36
  specialize h2 6
  rw [show 6 + 30 = 36 by ring_nf] at h2
  rw [show 2 ^ 6 - 1 = 63 by ring_nf] at h2
  have g1 : (1 / (2 * √2)) ^ 63 > 0:= by positivity
  set t:= (1 / (2 * √2)) ^ 63 with ht
  clear_value t
  replace h4 : t * (x 30 - √2) < t:= by exact mul_lt_of_lt_one_right g1 h4
  -- Show that t ≤ 10^(-9)
  suffices t ≤ 10 ^ (-9 : ℝ) by linarith
  set s:= 1 / (2 * √2) with hs
  clear_value s
  have g2 : s > 0:= by
    subst s
    positivity
  -- Show that s < 1/2
  replace hs : s < 1 / 2:= by
    subst s
    have g1 : (2 : ℝ) > 0:= by linarith
    suffices 2 * √2 > 2 by exact one_div_lt_one_div_of_lt g1 this
    suffices √2 > 1 by linarith
    have g2 : (2 : ℝ) ≥ (5 / 4) ^ 2:= by linarith
    replace g2 : √2 ≥ √((5 / 4) ^ 2):= by exact Real.sqrt_le_sqrt g2
    field_simp at g2
    linarith
  -- Use the fact that s^63 ≤ s^30
  have hs1 : s ^ 63 ≤ s ^ 30:= by
    rw [show s ^ 63 = s ^ 30 * s ^ 33 by ring_nf]
    have g1 : s ^ 30 ≥ 0:= by positivity
    suffices s ^ 33 ≤ 1 by exact mul_le_of_le_one_right g1 this
    replace g2 : s ≥ 0:= by linarith
    replace hs : s ≤ 1:= by linarith
    exact pow_le_one₀ g2 hs
  norm_num
  -- Final bound: s^30 ≤ (1/2)^30 and (1/2)^30 < 10^(-9)
  replace hs : s ^ 30 ≤ (1 / 2) ^ 30:= by
    replace g2 : s ≥ 0:= by linarith
    replace hs : s ≤ 1 / 2:= by linarith
    exact pow_le_pow_left g2 hs 30
  linarith
