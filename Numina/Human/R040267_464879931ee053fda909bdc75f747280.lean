import Mathlib
open Real
/- Déterminer tous les nombres réels $a$ tels qu'il existe une suite infinie de nombres réels strictement positifs $x_{0}, x_{1}, x_{2}, x_{3}, \ldots$ vérifiant pour tout $n$ l'égalité

$$
x_{n+2}=\sqrt{a x_{n+1}-x_{n}} .
$$ -/
theorem algebra_605518 (a : ℝ) : (∃ x : ℕ → ℝ, (∀ n, x (n + 2) = Real.sqrt (a * x (n + 1) - x n)) ∧
(∀ n, 0 < x n)) ↔ a > 1:= by
  constructor
  -- First direction: if such a sequence exists, then a > 1
  .
    intro h
    rcases h with ⟨x, hx, hn⟩
    by_contra H
    simp at H
    -- Prove that for all n, x_{n+1} > x_n
    have h2 : ∀ n : ℕ, x (n + 1) > x n:= by
      intro n
      have g1 : a * x (n + 1) ≤ 1 * x (n + 1):= by
        specialize hn (n + 1)
        exact (mul_le_mul_iff_of_pos_right hn).mpr H
      simp at g1
      specialize hx n
      specialize hn (n + 2)
      rw [hx] at hn
      simp at hn
      linarith
    -- Prove that for all n, x_{n+1} < 1
    have h3 : ∀ n : ℕ, x (n + 1) < 1:= by
      intro n
      specialize h2 (n + 1)
      rw [show n + 1 + 1 = n + 2 by ring] at h2
      specialize hx n
      -- Show that a*x_{n+1} - x_n > 0
      have g1 : a * x (n + 1) - x n > 0:= by
        specialize hn (n + 2)
        rw [hx] at hn
        simp at hn
        linarith
      -- Show that a*x_{n+1} - x_n < x_{n+1}
      have g2 : a * x (n + 1) - x n < x (n + 1):= by
        have g2 : a * x (n + 1) ≤ 1 * x (n + 1):= by
          specialize hn (n + 1)
          exact (mul_le_mul_iff_of_pos_right hn).mpr H
        specialize hn n
        linarith
      -- Apply square root to both sides of the inequality
      replace g2 : √(a * x (n + 1) - x n) < √(x (n + 1)):= by
        apply sqrt_lt_sqrt
        .
          linarith
        .
          linarith
      rw [←hx] at g2
      -- Derive that sqrt(x_{n+1}) * (1 - sqrt(x_{n+1})) > 0
      replace g2 : √(x (n + 1)) * (1 - √(x (n + 1))) > 0:= by
        specialize hn (1 + n)
        ring_nf
        field_simp
        rw [show 1 + n = n + 1 by ring]
        linarith
      specialize hn (n + 1)
      have hn1:= hn
      replace hn : √(x (n + 1)) > 0:= by positivity
      replace g2 : 1 - √(x (n + 1)) > 0:= by exact (pos_iff_pos_of_mul_pos g2).mp hn
      replace g2 : √(x (n + 1)) < 1:= by linarith
      replace h2 : √(x (n + 1)) ^ 2 < 1:= by refine (sq_lt_one_iff (by linarith)).mpr g2
      field_simp at h2
      exact h2
    -- Prove that for all n, x_{n+1} ≥ (1+x_0)*x_n
    have h4 : ∀ n : ℕ, x (n + 1) ≥ (1 + x 0) * x n:= by
      intro n
      specialize hx n
      have g1:= h2 (n + 1)
      rw [show n + 1 + 1 = n + 2 by ring] at g1
      have g2 : a * x (n + 1) ≤ 1 * x (n + 1):= by
        specialize hn (n + 1)
        exact (mul_le_mul_iff_of_pos_right hn).mpr H
      have g3 : a * x (n + 1) - x n > 0:= by
        specialize hn (n + 2)
        rw [hx] at hn
        simp at hn
        linarith
      replace g4 : √(a * x (n + 1) - x n) ≤ √(x (n + 1) - x n):= by
        apply sqrt_le_sqrt
        linarith
      replace g1 : x (n + 2) ^ 2 > x (n + 1) ^ 2:= by
        have g5:= hn (n + 1)
        refine pow_lt_pow_left (h2 (n + 1)) (by linarith) (by omega)
      rw [hx] at g1
      field_simp at g1
      simp at g2
      clear g3 g4
      have g3:= h2 n
      -- Show that x_n ≥ x_0 for all n
      have g4 : ∀ n : ℕ, x n ≥ x 0:= by
        intro n
        induction n with
        | zero =>
          simp
        | succ n hn =>
          specialize h2 n
          linarith
      specialize g4 (n + 1)
      replace g3 : x (n + 1) * x (n + 1) ≥ x n * x 0:= by refine mul_le_mul_of_nonneg (by linarith) g4 (by linarith only [hn n]) (by linarith only [hn (n + 1)])
      linarith
    -- Prove that x_n ≥ (1+x_0)^n * x_0 for all n
    replace h4 : ∀ n : ℕ, x n ≥ (1 + x 0) ^ n * x 0:= by
      intro n
      induction n with
      | zero =>
        simp
      | succ n hn1 =>
        specialize h4 n
        have g1 : 1 + x 0 ≥ 0:= by linarith only [hn 0]
        replace hn1 : (1 + x 0) * x n ≥ (1 + x 0) * ((1 + x 0) ^ n * x 0):= by exact mul_le_mul_of_nonneg_left hn1 g1
        rw [show (1 + x 0) ^ (n + 1) = (1 + x 0) * ((1 + x 0) ^ n) by ring]
        linarith
    have h5:= one_add_mul_le_pow (show x 0 ≥ -2 by linarith only [hn 0])
    -- Prove that x_n ≥ n*x_0^2 for all n
    replace h4 : ∀ n : ℕ, x n ≥ n * x 0 ^ 2:= by
      intro n
      specialize h4 n
      specialize h5 n
      specialize hn 0
      replace h5 : x 0 * (1 + n * x 0) ≤ x 0 * (1 + x 0) ^ n:= by exact (mul_le_mul_iff_of_pos_left hn).mpr h5
      linarith
    -- Define b = x_0^2
    set b:= x 0 ^ 2 with hb
    clear_value b
    replace hb : b > 0:= by
      subst b
      specialize hn 0
      positivity
    -- Define N = ⌊(1/b + 1)⌋
    set N:= ⌊(1 / b + 1)⌋.natAbs with hN
    clear_value N
    -- Prove that N*b ≥ 1
    have h6 : N * b ≥ 1:= by
      have g1 : N ≥ 1 / b:= by
        subst N
        rw [show (↑⌊1 / b + 1⌋.natAbs : ℝ) = (↑(↑⌊1 / b + 1⌋.natAbs : ℤ) : ℝ) by rfl]
        simp
        field_simp
        replace g2 : ⌊1 / b⌋ ≥ 0:= by positivity
        rify at g2
        rw [abs_of_nonneg (by linarith)]
        have g3 : ⌊1 / b⌋ > 1 / b - 1:= by exact Int.sub_one_lt_floor (1 / b)
        linarith
      exact (mul_inv_le_iff₀ hb).mp g1
    -- Derive a contradiction using the bounds on x_n
    specialize h4 (N + 1)
    simp at h4
    specialize h3 N
    linarith
  -- Second direction: if a > 1, then such a sequence exists
  .
    intro h
    -- Define the constant sequence x_n = a-1 for all n
    use (fun n => a - 1)
    constructor
    -- Verify that the sequence satisfies the recurrence relation
    .
      simp
      rw [show a * (a - 1) - (a - 1) = (a - 1) ^ 2 by ring]
      replace h : a - 1 > 0:= by linarith
      field_simp
    -- Verify that all terms of the sequence are positive
    .
      simp
      linarith
