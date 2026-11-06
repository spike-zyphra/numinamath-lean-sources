import Mathlib

open Topology Filter Real

-- If 0 ≤ x n and √(n * x n + n + 1) - √(n * x n + 1) ≤ √n / 2 for all n > 0
-- then 9 / 16 - 1 / n ≤ x n for sufficiently large n.
lemma lemma_1 (x : ℕ → ℝ) (hx0 : ∀ n, 0 ≤ x n)
    (h : ∀ n : ℕ, 0 < n → √(n * x n + n + 1) - √(n * x n + 1) ≤ √n / 2) :
    ∀ᶠ n in atTop, 9 / 16 - 1 / n ≤ x n := by
  simp only [tsub_le_iff_right, eventually_atTop, ge_iff_le]
  -- Show that 9 / 16 - 1 / n ≤ x n for n ≥ 1.
  use 1
  intro n hn
  apply of_iff_true
  calc
    -- We have 9 / 16 ≤ x n + 1 / n ↔ 3 / 4 ≤ √(x n + 1 / n)
    --    ↔ 1 + x n + 1 / n ≤ 1 / 4 + (x n + √(x n + 1 / n) + 1 / n)
    --    ↔ √n * √(1 + x n + 1 / n) ≤ √n * (1 / 2 + √(x n + 1 / n))
    --    ↔ √(n * x n + n + 1) - √(n * x n + 1) ≤ √n / 2.
    9 / 16 ≤ x n + 1 / n ↔ √((3 / 4)^2) ≤ √(x n + 1 / n) := by
      have := hx0 n
      rw [sqrt_le_sqrt_iff (by positivity)]
      norm_num
    _ ↔ 1 + x n + 1 / n ≤ 1 / 4 + (x n + √(x n + 1 / n) + 1 / n) := by
      rw [sqrt_sq (by norm_num), ← sub_nonneg, ← sub_nonneg (b := 1 + x n + 1 / n)]
      ring_nf
    _ ↔ √n * √(1 + x n + 1 / n) ≤ √n * (1 / 2 + √(x n + 1 / n)) := by
      rw [mul_le_mul_left (by positivity)]
      nth_rw 2 [← sq_le_sq₀ (by positivity) (by positivity)]
      have := hx0 n
      ring_nf
      repeat rw [sq_sqrt (by positivity)]
      ring_nf
    _ ↔ √(n * x n + n + 1) - √(n * x n + 1) ≤ √n / 2 := by
      rw [mul_add, ← sqrt_mul (by positivity), ← sqrt_mul (by positivity)]
      simp_rw [mul_add, show n * ((1 : ℝ) / n) = 1 by field_simp]
      simp [← sub_nonneg]
      ring_nf
    _ ↔ True := by
      rw [iff_true]
      exact h n (by linarith)

-- If 0 ≤ x n and √n / 2 ≤ √(n * x n + n) - √(n * x n) for all n > 0
-- then x n ≤ 9 / 16 for sufficiently large n.
lemma lemma_2 (x : ℕ → ℝ) (hx0 : ∀ n, 0 ≤ x n)
    (h : ∀ n : ℕ, 0 < n → √n / 2 ≤ √(n * x n + n) - √(n * x n)) :
    ∀ᶠ n in atTop, x n ≤ 9 / 16 := by
  simp only [eventually_atTop, ge_iff_le]
  -- Show that x n ≤ 9 / 16 for n ≥ 1.
  use 1
  intro n hn
  apply of_iff_true
  calc
    -- We have
    -- x n ≤ 9 / 16 ↔ √(x n) ≤ 3 / 4
    --     ↔ 1 / 4 + x n + √(x n) ≤ 1 + x n
    --     ↔ √n * (1 / 2 + √(x n)) ≤ √n * √(1 + x n)
    --     ↔ √n / 2 ≤ √(n * x n + n) - √(n * x n).
    x n ≤ 9 / 16 ↔ √(x n) ≤ √((3 / 4)^2) := by
      rw [sqrt_le_sqrt_iff (by positivity)]
      norm_num
    _ ↔ 1 / 4 + x n + √(x n) ≤ 1 + x n := by
      rw [sqrt_sq (by norm_num), ← sub_nonneg, ← sub_nonneg (a := 1 + x n)]
      ring_nf
    _ ↔ √n * (1 / 2 + √(x n)) ≤ √n * √(1 + x n) := by
      rw [mul_le_mul_left (by positivity)]
      nth_rw 2 [← sq_le_sq₀ (by positivity) (by positivity)]
      have := hx0 n
      ring_nf
      repeat rw [sq_sqrt (by positivity)]
      ring_nf
    _ ↔ √n / 2 ≤ √(n * x n + n) - √(n * x n) := by
      rw [mul_add, ← sqrt_mul (by positivity), ← sqrt_mul (by positivity), mul_add]
      simp [← sub_nonneg]
      ring_nf
    _ ↔ True := by
      rw [iff_true]
      exact h n (by linarith)


/- ## Problem 4.
Let $\left(x_{n}\right)_{n \geq 1}$ be a sequence of real numbers with the property that
$$
\sqrt{n \cdot x_{n}+n+1}-\sqrt{n \cdot x_{n}+1} \leq \frac{\sqrt{n}}{2} \leq \sqrt{n \cdot x_{n}+n}-\sqrt{n \cdot x_{n}},(\forall) n \geq 1
$$
Calculate the limit of the sequence $\left(x_{n}\right)_{n \geq 1}$. -/
theorem inequalities_117769 (x : ℕ → ℝ)
    (hx0 : ∀ n, 0 ≤ x n)
    (h : ∀ n, 0 < n → √(n * x n + n + 1) - √(n * x n + 1) ≤
      √n / 2 ∧ √n / 2 ≤ √(n * x n + n) - √(n * x n)) :
    Tendsto x atTop (𝓝 (9 / 16)) := by
  -- lemma_1 and lemma_2 imply that
  -- 9 / 16 - 1 / n ≤ x n ≤ 9 / 16.
  -- Apply the squeeze theorem to x(n).
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _ _
          (lemma_1 x hx0 (fun n hn => (h n hn).1))
          (lemma_2 x hx0 (fun n hn => (h n hn).2))
  · -- Show that lim(9 / 16 - 1 / n) = 9 / 16.
    nth_rw 2 [show (9 : ℝ) / 16 = 9 / 16 - 0 by norm_num]
    apply Tendsto.const_sub
    exact tendsto_one_div_atTop_nhds_zero_nat
  · -- Show that lim(9 / 16) = 9 / 16.
    exact tendsto_const_nhds