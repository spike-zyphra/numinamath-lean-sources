import Mathlib

open Real Finset

/- Let $a>2$ be given, and define a sequence $a_{0}, a_{1}, a_{2}, \ldots$ by
$$
a_{0}=1, \quad a_{1}=a, \quad a_{n+1}=\left(\frac{a_{n}^{2}}{a_{n-1}^{2}}-2\right) \cdot a_{n} .
$$
Show that for all integers $k \geq 0$, we have
$$
\sum_{i=0}^{k} \frac{1}{a_{i}}<\frac{a+2-\sqrt{a^{2}-4}}{2} .
$$
 -/
theorem algebra_254237 {a : ℝ} (ha : a > 2)
    (a' : ℕ → ℝ) (h_a0 : a' 0 = 1) (h_a1 : a' 1 = a)
    (h_an : ∀ n ≥ 1, a' (n + 1) = ((a' n)^2 / (a' (n - 1))^2 - 2) * a' n) :
    ∀ k, ∑ i in Icc 0 k, (1 / a' i) < ((a + 2 - sqrt (a^2 - 4)) / 2) := by
  -- Show that 0 < a' n for all n.
  have h0 n : 0 < a' n := by
    -- Prove a stronger statement: 0 < a' n and 2 ≤ a' (n + 1) / a' n.
    suffices 0 < a' n ∧ 2 ≤ a' (n + 1) / a' n by exact this.1
    -- Proof by induction.
    induction n with
    -- If n = 0 then a' 0 = 1 > 0 and a' 1 / a' 0 = a > 2.
    | zero => simp [h_a0, h_a1, le_of_lt ha]
    | succ n ih =>
      -- Consider n + 1. We have 0 < a' n and 2 ≤ a' (n + 1) / a' n.
      have ⟨ih0, ih2⟩ := ih
      -- Show that 0 < a' (n + 1): 0 < 2 * a' n ≤ a' (n + 1).
      have h1 : 0 < a' (n + 1) := by
        rw [le_div_iff₀ ih0] at ih2
        linarith
      simp [h1]
      -- Show that 2 ≤ a' (n + 2) / a' (n + 1)
      --     = (a' (n + 1) ^ 2 / a' n ^ 2 - 2) * a ' (n + 1) / a' (n + 1)
      --     = (a' (n + 1) / a' n)^2 - 2
      --     ≥ 4 - 2 = 2.
      rw [h_an (n + 1) (by linarith)]
      rw [mul_div_cancel_right₀ _ (by positivity), ← div_pow, show n + 1 - 1 = n by omega]
      nlinarith
  -- Define b(n) = a'(n + 1) / a'(n).
  set b : ℕ → ℝ := fun n => a' (n + 1) / a' n
  -- We have b(0) = a.
  have hb0 : b 0 = a := by simp [b, h_a1, h_a0]
  -- We have b(n + 1) = b(n)^2 - 2.
  have hb n : b (n + 1) = b n ^ 2 - 2 := by
    simp [b, h_an (n + 1)]
    rw [mul_div_cancel_right₀ _ (ne_of_gt <| h0 (n + 1)), div_pow]
  -- Define t = (a + √(a^2 - 4)) / 2.
  set t : ℝ := (a + √(a^2 - 4)) / 2
  -- We have a = t + 1 / t.
  have ht : a = t + 1 / t := by
    field_simp [t]
    ring_nf
    rw [sq_sqrt (by nlinarith)]
    ring
  -- We have 1 < t (because 2 < a).
  have ht1 : 1 < t := by
    simp [t]
    suffices 0 ≤ √(a ^ 2 - 4) by linarith
    positivity
  -- We have 1 < t^n for all 0 < n.
  have ht1' {n : ℕ} (hn : 0 < n) : 1 < t^n := by
    apply one_lt_pow₀ ht1 (by linarith)
  -- Show that b(n) = t^2^n + 1 / t^2^n.
  have hbt n : b n = t^2^n + 1 / t^2^n := by
    -- Proof by induction.
    induction n with
    -- a = b(0) = t + 1 / t.
    | zero => simp [hb0, ht]
    | succ n ih =>
      -- b(n + 1) = b(n)^2 - 2 = (t^2^n + 1 / t^2^n)^2 - 2 = t^2^(n + 1) + 1 / t^2^(n + 1).
      rw [hb, ih]
      field_simp
      ring
  -- Show that a'(n) = (t^2^n - 1 / t^2^n) / (t - 1 / t).
  have hat n : a' n = (t^2^n - 1 / t^2^n) / (t - 1 / t) := by
    -- Proof by induction.
    induction n with
    | zero =>
      -- a'(0) = 1 = (t - 1 / t) / (t - 1 / t).
      simp [h_a0]
      rw [div_self]
      field_simp
      nlinarith
    | succ n ih =>
      -- a'(n + 1) = b(n) * a'(n)
      --           = (t^2^n + 1 / t^2^n) * (t^2^n - 1 / t^2^n) / (t - 1 / t)
      --           = (t^2^(n + 1) - 1 / t^2^(n + 1)) / (t - 1 / t).
      have eq : a' (n + 1) = b n * a' n := by
        simp [b]
        rw [div_mul_cancel₀ _ (by linarith [h0 n])]
      rw [eq, ih, hbt]
      rw [mul_div]
      congr
      ring
  intro k
  -- Prove that ∑ i ∈ [0, k], 1 / a'(i) < (a + 2 - √(a^2 - 4)) / 2.
  calc
    -- Rewrite the sum as
    -- (t - 1 / t) * ∑ i ∈ Icc 0 k, 1 / (t^2^i - 1 / t^2^i).
    _ = (t - 1 / t) * ∑ i ∈ Icc 0 k, 1 / (t^2^i - 1 / t^2^i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      simp [hat]
      rfl
    -- We have 1 / (t^2^i - 1 / t^2^i) = 1 / (t^2^i - 1) - 1 / (t^2^(i + 1) - 1)
    -- for all i.
    _ = (t - 1 / t) * ∑ i ∈ Icc 0 k, (1 / (t^2^i - 1) - 1 / (t^2^(i + 1) - 1)) := by
      congr 1
      apply sum_congr rfl
      intro i hi
      field_simp
      have hineq1 := ht1' (show 0 < 2^i by positivity)
      have hineq2 := ht1' (show 0 < 2^(i + 1) by positivity)
      rw [div_sub_div _ _ (by linarith) (by linarith)]
      simp only [one_mul, mul_one, sub_sub_sub_cancel_right]
      rw [show t^2^(i + 1) - t^2^i = (t^2^i - 1) * t^2^i by ring]
      rw [mul_div_mul_left _ _ (by linarith)]
      congr
      ring
    -- The sum simplifies to
    -- 1 / (t - 1) - 1 / (t^2^(k + 1) - 1).
    _ = (t - 1 / t) * (1 / (t - 1) - 1 / (t^2^(k + 1) - 1)) := by
      congr
      have eq : Finset.Icc 0 k = range (k + 1) := by ext i; simp; omega
      rw [eq, Finset.sum_range_sub']
      simp only [pow_zero, pow_one, one_div]
    -- 0 < 1 / t^2^(k + 1) - 1, so
    -- (t - 1 / t) * (1 / (t - 1) - 1 / (t^2^(k + 1) - 1)) < (t - 1 / t) * (1 / (t - 1)).
    _ < (t - 1 / t) * (1 / (t - 1)) := by
      gcongr
      · field_simp
        nlinarith
      · suffices 0 < 1 / (t^2^(k + 1) - 1) by linarith
        field_simp
        apply ht1'
        positivity
    -- (t - 1 / t) * (1 / (t - 1)) = 1 + 1 / t.
    _ = 1 + 1 / t := by
      field_simp [show t * (t - 1) ≠ 0 by nlinarith]
      ring
    -- 1 + 1 / t = (a + 2 - √(a^2 - 4)) / 2.
    _ = (a + 2 - √(a^2 - 4)) / 2 := by
      field_simp [t]
      ring_nf
      rw [sq_sqrt (by nlinarith)]
      ring