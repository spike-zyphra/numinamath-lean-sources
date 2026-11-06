import Mathlib

/- Let $a_{0}>0$ be a real number, and let

$$
a_{n}=\frac{a_{n-1}}{\sqrt{1+2020 \cdot a_{n-1}^{2}}}, \quad \text { for } n=1,2, \ldots, 2020
$$

Show that $a_{2020}<\frac{1}{2020}$. -/
theorem algebra_606369 (a : ℕ → ℝ) (h0 : a 0 > 0) (hn : ∀ n : ℕ, a (n + 1) = a n / √(1 + 2020 * (a n) ^ 2)) : a 2020 < 1 / 2020 := by
  -- First prove that all terms in sequence are positive
  have hpos : ∀ n : ℕ, a n > 0 := by
    intro n
    induction n with
    | zero =>
      exact h0
    | succ n ih =>
      specialize hn n
      rw [hn]
      positivity

  -- Define a new sequence b_n = 1/(a_n)^2 to simplify the problem
  set b : ℕ → ℝ:= fun n => 1 / (a n) ^ 2 with hb
  clear_value b

  -- Show b_0 is positive
  replace h0 : b 0 > 0 := by
    simp [hb]
    positivity

  -- Prove that b_(n+1) = b_n + 2020, showing b_n is an arithmetic sequence
  replace hn : ∀ n : ℕ, b (n + 1) = b n + 2020 := by
    intro n
    simp [hb]
    specialize hn n
    rw [hn]
    specialize hpos n
    field_simp

  -- Therefore b_n = 2020*n + b_0 (explicit formula for arithmetic sequence)
  replace hn : ∀ n : ℕ, b n = 2020 * n + b 0 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      specialize hn n
      rw [hn, ih]
      simp
      linarith

  -- Focus on n = 2020 case
  specialize hn 2020
  simp at hn
  -- Show b_2020 > 2020^2
  replace hn : b 2020 > 2020 ^ 2:= by linarith
  simp [hb] at hn
  field_simp at hn

  -- Use positivity of a_2020^2
  specialize hpos 2020
  replace hpos : (a 2020) ^ 2 > 0 := by positivity

  -- Key inequality manipulation
  replace hn : (a 2020) ^ 2 * 2020 ^ 2 < (a 2020) ^ 2 * (1 / a 2020 ^ 2):= by exact (mul_lt_mul_left hpos).mpr hn
  rw [show (a 2020) ^ 2 * (1 / a 2020 ^ 2) = 1 by field_simp] at hn
  rw [show a 2020 ^ 2 * 2020 ^ 2 = (a 2020 * 2020) ^ 2 by ring] at hn

  -- Final steps: prove a_2020 * 2020 < 1, which implies a_2020 < 1/2020
  replace hn : a 2020 * 2020 < 1 := by
    by_contra H
    simp at H
    replace H : (a 2020 * 2020) ^ 2 ≥ 1:= by nlinarith only [H]
    linarith
  linarith
