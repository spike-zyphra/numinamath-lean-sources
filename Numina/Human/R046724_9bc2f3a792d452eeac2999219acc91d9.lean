import Mathlib

/- Problem 2. Show that the number

$$
\sqrt[n]{\sqrt{2018}+\sqrt{2017}}+\sqrt[n]{\sqrt{2018}-\sqrt{2017}}
$$
is irrational, for any $n \geq 2$.

Mathematical Gazette -/
theorem number_theory_113420 (n : ℕ) (hn : 2 ≤ n) :
    Irrational ((Real.sqrt 2018 + Real.sqrt 2017) ^ (1 / n : ℝ) +
      (Real.sqrt 2018 - Real.sqrt 2017) ^ (1 / n : ℝ)) := by
  have ineq1 : 0 < √2018 - √2017 := by
    rw [sub_pos]
    apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- Let a = (√2018 + √2017)^(1 / n)
  set a := (√2018 + √2017) ^ (1 / n : ℝ)
  -- Let b = (√2018 - √2017)^(1 / n)
  set b := (√2018 - √2017) ^ (1 / n : ℝ)
  -- Define s(k) = a^k + b^k.
  set s : ℕ → ℝ := fun k => a ^ k + b ^ k
  -- We have to show that a + b = s(1) is irrational.
  -- We have a * b = 1.
  have hab : a * b = 1 := by
    dsimp [a, b]
    -- (√2018 + √2017) * (√2018 - √2017) = 2018 - 2017 = 1.
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    ring_nf
    rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
    norm_num
  -- Prove the following recursive formula for s:
  -- s (k + 2) = (a + b) * s (k + 1) - s k
  have hs k : s (k + 2) = (a + b) * s (k + 1) - s k := by
    -- The result follows from the definition of s(n):
    -- s(k + 2) = a^(k + 2) + b^(k + 2) = (a + b) * (a^(k + 1) + b^(k + 1)) - a * b * (a^k + b^k)
    --          = (a + b) * s(k + 1) - s(k) (because a * b = 1).
    rw [← one_mul (s k), ← hab]
    simp_rw [s]
    ring
  simp [Irrational]
  -- Assume that s(1) = a + b is not irrational. Then there exists a rational number q such that
  -- q = a + b.
  by_contra! h
  have ⟨q, hq⟩ := h
  -- Prove that s(k) is rational for all k.
  let rec h : (k : ℕ) → ∃ p : ℚ, s k = p
  -- s(0) is rational because s(0) = 2.
  | 0 => by
    simp [s]
    use 2
    norm_num
  -- s(1) = a + b = q is rational.
  | 1 => by
    simp [s]
    use q
    rw [hq]
  -- Consider s(k + 2) = (a + b) * s(k + 1) - s(k) = q * r - p
  -- where p and r are rational number from the induction hypothesis.
  | k + 2 => by
    have ⟨p, hp⟩ := h k
    have ⟨r, hr⟩ := h (k + 1)
    use q * r - p
    rw [hs, hr, hp, ← hq]
    norm_cast
  -- We get s(n) = p ∈ ℚ.
  have ⟨p, hp⟩ := h n
  simp_rw [s, a, b, ← Real.rpow_natCast] at hp
  -- Simplify s(n) and get s(n) = 2 * √2018 = p.
  repeat rw [← Real.rpow_mul (by positivity), show 1 / (n : ℝ) * n = 1 by field_simp, Real.rpow_one] at hp
  ring_nf at hp
  -- Show that s(n) ≠ p ∈ ℚ and derive a contradiction.
  apply_fun Irrational at hp
  -- It is enough to show that s(n) is irrational.
  simp at hp
  apply hp
  rw [show (2018 : ℝ) = (2018 : ℕ) by simp]
  rw [show (2 : ℝ) = (2 : ℕ) by simp]
  apply Irrational.mul_nat _ (by norm_num)
  simp_rw [irrational_sqrt_natCast_iff, IsSquare]
  -- We need to demonstrate that 2018 is not a square.
  -- In other words, 2018 ≠ r * r for all natural r.
  push_neg
  intro r
  rw [← pow_two]
  -- Consider two cases: r ≤ 44 and 45 ≤ r.
  cases' show r ≤ 44 ∨ 45 ≤ r by omega with h h
  · apply ne_of_gt
    -- If r ≤ 44 then r * r ≤ 44 * 44 < 2018.
    apply lt_of_le_of_lt _ (show 44 ^ 2 < 2018 by norm_num)
    exact Nat.pow_le_pow_left h _
  · apply ne_of_lt
    -- If 45 ≤ r then 2018 < 45 * 45 ≤ r * r.
    apply lt_of_lt_of_le (show 2018 < 45 ^ 2 by norm_num)
    exact Nat.pow_le_pow_left h _