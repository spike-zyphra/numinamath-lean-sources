import Mathlib

open Finset
open BigOperators

/-- Given the numbers $x_1, x_2, x_3, \cdots, x_{2018}$. It is known that $x_1 = \frac{1}{2}$ and 
$$x_n = \frac {x_{n-1}} {2n x_{n-1} + 1} for n = 2, \cdots, 2018$$. Find the sum $x_1 + x_2 + \cdots + x_{2018}$ .-/
theorem RecursionOther_4202
      (f : ℕ → ℚ) (hf_ne0 : ∀ n, f n ≠ 0)
      (hf_1 : f 1 = 1 / 2)
      (hf_other : ∀ n > 1, f n = f (n - 1) / (2 * n * f (n - 1) + 1))
      : ∑ i ∈ range 2018, f (i+1) = 2018 / 2019 := by

  -- Construct auxiliary sequence $g = \frac 1 f$
  let g (n : ℕ) := 1 / f n

  -- The recurrence relation of g
  have hg_1 : g 1 = 2 := by simp [g, hf_1]
  have hg_other {n : ℕ} (hn : n > 1) : g n = 2 * n + g (n - 1) := by
    simp [g]
    rw [hf_other n hn, inv_div (f (n - 1)) (2 * ↑n * f (n - 1) + 1)]
    rw [add_div (2 * (n:ℚ) * f (n - 1)) 1 (f (n - 1))]
    rw [mul_div_cancel_right₀ (2 * (n:ℚ)) (hf_ne0 (n - 1))]
    simp

  --The general term of g
  have g_term {n : ℕ} (hn : n > 0) : g n = n * (n + 1) := by
    induction n with
    | zero => linarith
    | succ n ih =>
    cases n with
      | zero => simp [hg_1]; norm_num
      | succ n =>
        rw [hg_other (by linarith), Nat.add_sub_cancel (n+1) 1, ih (by linarith)]
        simp [mul_add, add_mul]; ring
  let qp (n : ℕ) := - 1 / (n.succ : ℚ)

  -- The general term of f
  have f_term {n : ℕ} (hn : n > 0) : f n = 1 / n - 1 / (n + 1) := by
    rw [show f n = 1 / g n by simp [g], g_term hn]
    field_simp

  -- Sum the arithmetic progression
  have : ∑ i ∈ range 2018, f (i+1) = ∑ i ∈ range 2018, (qp (i+1) - qp i) := by
    apply Finset.sum_congr rfl
    intros x hx; rw [f_term (by linarith)]
    simp at hx; simp [qp]; ring_nf;

  rw [this]
  rw [Finset.sum_range_sub]
  simp [qp]
  norm_num
