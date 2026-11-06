import Mathlib

/- 7. Given real numbers $a, b (b > a > 1)$. Let
$$
x_{n}=2^{n}(\sqrt[2^{n}]{b}-\sqrt[2^{n}]{a}) \text {. }
$$
Prove: The sequence $x_{1}, x_{2}, \cdots$ is strictly monotonically decreasing. -/
theorem calculus_273185 {a b : ℝ} (ha : 1 < a) (hb : a < b)
    (x : ℕ → ℝ) (hx : ∀ n, x n = 2 ^ n * (b ^ ((1 : ℝ) / (2 ^ n)) - a ^ ((1 : ℝ) / (2 ^ n)))) :
    StrictAnti x := by
  -- It is enough to show that x(n + 1) < x(n) for all n.
  apply strictAnti_nat_of_succ_lt
  intro n
  -- Define A = a^(1/2^(n + 1))
  set A := a ^ ((1 : ℝ) / (2 ^ (n + 1)))
  -- Define B = b^(1/2^(n + 1))
  set B := b ^ ((1 : ℝ) / (2 ^ (n + 1)))
  -- We have 1 < A (since 1 < a).
  have hA : 1 < A := Real.one_lt_rpow ha (by positivity)
  -- We have 1 < B (since 1 < b).
  have hB : 1 < B := Real.one_lt_rpow (lt_trans ha hb) (by positivity)
  -- We have A < B (since a < b).
  have hAB : A < B := Real.rpow_lt_rpow (by linarith) hb (by positivity)
  calc
    -- x(n + 1) = 2^(n + 1) * (B - A)
    --          < 2^(n + 1) * (B - A) * ((A + B) / 2) (because (A + B) / 2 > 1)
    --          = 2^n * (B^2 - A^2)
    --          = x(n) (because B^2 = b^(1/2^n) and A^2 = a^(1/2^n)).
    x (n + 1) = 2 ^ (n + 1) * (B - A) * 1 := by simp_rw [hx, A, B, mul_one]
    _ < 2 ^ (n + 1) * (B - A) * ((A + B) / 2) := by
      gcongr
      · apply mul_pos (by positivity) (by linarith)
      · linarith
    _ = 2 ^ n * (B ^ 2 - A ^ 2) := by ring
    _ = x n := by
      simp_rw [hx, A, B, ← Real.rpow_natCast _ 2]
      repeat rw [← Real.rpow_mul (by linarith)]
      suffices (1 : ℝ) / 2 ^ (n + 1) * (2 : ℕ) = 1 / 2 ^ n by rw [this]
      ring