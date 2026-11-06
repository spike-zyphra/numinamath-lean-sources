import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators


/-
Let $x_{0}$ and $y_{0}$ be some positive numbers,
with $x_{0}>y_{0}, x_{n+1}=\frac{x_{n}+y_{n}}{2}$ and $y_{n+1}=\sqrt{x_{n} y_{n}}$
for $n \geqslant 0$.
Prove that both sequences $\left\{x_{n}\right\}$ and $\left\{y_{n}\right\}$
converge to the same limit,
called the arithmetic-geometric mean of the numbers $x_{0}$ and $y_{0}$ (Gauss).
-/
theorem algebra_228304
  (x y : ℕ → ℝ)
  (hx0 : 0 < x 0)
  (hy0 : 0 < y 0)
  (hxy : x 0 > y 0)
  (hxn : ∀ n, x (n + 1) = (x n + y n) / 2)
  (hyn : ∀ n, y (n + 1) = Real.sqrt (x n * y n)) :
  ∃ L, Tendsto x atTop (𝓝 L) ∧ Tendsto y atTop (𝓝 L) := by
    -- We show that both $ 0 < x_n $ and $ 0 < y_n $ for all $n \in \mathbb{N}$
    have xy_pos (n : ℕ) : 0 < x n ∧ 0 < y n := by
      induction n
      case zero => exact ⟨hx0, hy0⟩
      case succ k hk =>
        split_ands
        · rw [hxn]
          linarith
        · rw [hyn]
          rw [sqrt_pos]
          apply mul_pos hk.left hk.right
    have x_pos (n : ℕ) : 0 < x n := (xy_pos n).left
    have y_pos (n : ℕ) : 0 < y n := (xy_pos n).right
    -- We show that $x$ is antitone, $y$ is monotone and $y_n < x_n$ for all $ n \in \mathbb{N}$
    have xy (n : ℕ) : x (n + 1) < x n ∧ y n < y (n + 1) ∧ x n > y n := by
      induction n
      case zero =>
        split_ands
        · rw [hxn]
          linarith
        · rw [hyn]
          rw [lt_sqrt (le_of_lt hy0), sq]
          rw [mul_lt_mul_right hy0]
          exact hxy
        · exact hxy
      case succ k hk =>
        have y_lt_x :  y (k + 1) < x (k + 1) := by
          rw [hxn, hyn]
          have add_pos : 0 < (x k + y k) / 2 := by
            apply div_pos ?_ (by norm_num)
            apply add_pos (x_pos _) (y_pos _)
          rw [sqrt_lt (le_of_lt <| (mul_pos (x_pos _) (y_pos _))) (le_of_lt add_pos)]
          field_simp
          rw [lt_div_iff₀ (by norm_num), mul_assoc, mul_comm (y k),
            ← mul_assoc, mul_comm (x k), (by norm_num : (2 : ℝ)^2 = 4)]
          -- We use the AM-GM inequality
          apply lt_of_le_of_ne (four_mul_le_sq_add _ _)
          -- If equality in the AM-GM inequality is achieved then $a = b$
          · intro sq_eq_zero
            rw [add_sq'] at sq_eq_zero
            symm at sq_eq_zero
            rw [← sub_eq_zero] at sq_eq_zero
            ring_nf at sq_eq_zero
            rw [add_comm _ ((x k)^2),mul_assoc, mul_comm _ 2, ← mul_assoc, mul_comm _ 2,
              ← sub_eq_add_neg, ← sub_sq, sq_eq_zero_iff, sub_eq_zero] at sq_eq_zero
            -- contradiction since $ y_k < x_k $
            linarith
        split_ands
        · rw [hxn]
          rw [div_lt_iff₀ (by norm_num), mul_two]
          apply add_lt_add_left y_lt_x
        · nth_rewrite 2 [hyn]
          apply lt_of_le_of_lt (b := √(y (k + 1)* y (k + 1)))
          · rw [← sq, sqrt_sq (le_of_lt (y_pos _))]
          · apply sqrt_lt_sqrt (le_of_lt <| mul_pos (y_pos _) (y_pos _))
            rw [mul_lt_mul_right (y_pos _)]
            exact y_lt_x
        · exact y_lt_x
    have x_succ_lt_x (n : ℕ) : x (n + 1) < x n := (xy n).left
    have y_lt_y_succ (n : ℕ) : y n < y (n + 1) := (xy n).right.left
    have y_lt_x (n : ℕ) : y n < x n := (xy n).right.right
    -- The sequence $y_n$ is monotonously increasing
    have Monotone_y : Monotone y := by
      apply monotone_of_le_succ
      simp only [not_isMax, not_false_eq_true, Nat.succ_eq_succ, Nat.succ_eq_add_one, forall_const]
      intro n
      exact le_of_lt (y_lt_y_succ n)
    -- Sequence $x_n$ is shown to be monotone decreasing
    have Antitone_x : Antitone x := by
      apply antitone_of_succ_le
      simp only [not_isMax, not_false_eq_true, Nat.succ_eq_succ, Nat.succ_eq_add_one, forall_const]
      intro n
      exact le_of_lt (x_succ_lt_x n)
    -- The sequence $y$ is bounded above by $ x_0 $
    have BddAbove_y : BddAbove (Set.range y) := by
      use x 0
      rw [mem_upperBounds]
      simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      intro n
      apply le_trans (b := x n)
      apply le_of_lt (y_lt_x _)
      apply Antitone_x
      exact Nat.zero_le n
    -- The sequence $x$ is bounded below by $y_0$
    have BddBelow_x : BddBelow (Set.range x) := by
      use y 0
      rw [mem_lowerBounds]
      simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      intro n
      apply le_trans (b := y n)
      apply Monotone_y
      exact Nat.zero_le n
      exact le_of_lt (y_lt_x _)
    -- The monotone convergence theorem guarantees $ y $ converges to some limit $L_y$
    obtain ⟨Ly, hLy⟩ := Real.tendsto_of_bddAbove_monotone BddAbove_y Monotone_y
    -- The monotone convergence theorem guarantees $ x $ converges to some limit $L_x$
    obtain ⟨Lx, hLx⟩ := Real.tendsto_of_bddBelow_antitone BddBelow_x Antitone_x
    -- $ x_0 > \frac{x_0 + y_0}{2} > \sqrt{x_0 y_0} > y_0$
    use Lx
    refine ⟨hLx, ?Lx_eq_Ly⟩
    suffices Lx = Ly by
      rw [this]
      exact hLy
    let g : ℕ → ℝ := fun n => (x n) - ((x n) + (y n)) / 2
    have IsContinuous : Continuous g := by
      dsimp [g]
      continuity
    -- The sum, division by a constant and shifting of
    have key := Filter.Tendsto.add ((Filter.tendsto_add_atTop_iff_nat 1).mpr hLx)
      <| Filter.Tendsto.neg <| Filter.Tendsto.mul_const (1 / 2) (Filter.Tendsto.add hLx hLy)
    conv at key in (fun k => _) =>
      ext k
      rw [mul_div, mul_one, ← sub_eq_add_neg]
    conv at key in (𝓝 _) =>
      rw [mul_div, mul_one, ← sub_eq_add_neg]
    have eq_const : ∀ k ≥ 0, x (k + 1) - (x k + y k) / 2 = 0 := by simp [hxn]
    -- An eventually constant sequence converges to the constant
    have tendsto_zero := tendsto_atTop_of_eventually_const eq_const
    -- A sequence converges to a unique limit, thus $L_x - (L_x + L_y) / 2 = 0$
    -- which is equivalent to $L_x = L_y$
    have Lx_eq_Ly := tendsto_nhds_unique key tendsto_zero
    field_simp [mul_two, sub_eq_zero] at Lx_eq_Ly
    exact Lx_eq_Ly