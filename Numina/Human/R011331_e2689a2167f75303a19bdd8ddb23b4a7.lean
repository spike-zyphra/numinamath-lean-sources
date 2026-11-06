import Mathlib

/- Prove that there exist infinitely many $n \in \mathbb{N}^*$ such that $\sqrt{2n^2 + 2n + 1} \in \mathbb{N}^*$. -/
theorem number_theory_612314 : Set.Infinite {(n, m) : ℕ × ℕ | n > 0 ∧ m > 0 ∧ m ^ 2 = 2 * n ^ 2 + 2 * n + 1} := by
  -- Let x = 2n + 1, y = 2m, then we get Pell's equation x^2 - 2y^2 = -1.
  -- We can set x_n + y_n √2 = (1 + √2) * (3 + 2√2) ^ n
  -- The solutions are given by x_0 = 1, y_0 = 1, and x_{n+1} = 3x_n + 4y_n, y_{n+1} = 2x_n + 3y_n.
  -- The solution (1, 1) does not work because n = 0 is not positive, so we start from the next solution (7, 5).
  -- Use p(n) to denote the nth solution pair (x_n, y_n).
  let p (n : ℕ) : ℕ × ℕ := Nat.rec (7, 5) (fun _ (x, y) => (3 * x + 4 * y, 2 * x + 3 * y)) n
  -- Extract x_n and y_n from p(n).
  let x n := (p n).1
  let y n := (p n).2
  -- We get the initial values and the recurrence relations.
  have hx₀ : x 0 = 7 := by simp [x, p]
  have hy₀ : y 0 = 5 := by simp [y, p]
  have hx (n : ℕ) : x (n + 1) = 3 * x n + 4 * y n := by simp [x, y, p]
  have hy (n : ℕ) : y (n + 1) = 2 * x n + 3 * y n := by simp [x, y, p]
  -- We show y_n > 0 for all n and x_n ≥ 2 for all n by simple induction.
  have hypos (n : ℕ) : 0 < y n := by
    induction n with
    | zero => simp [hy₀]
    | succ n ih => simp [hy n, ih]
  have hxpos (n : ℕ) : 2 ≤ x n := by
    induction n with
    | zero => simp [hx₀]
    | succ n ih => specialize hx n; omega
  -- We show y_n is strictly increasing.
  have hymono : StrictMono y := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    specialize hy n
    specialize hypos n
    omega
  -- Key step: prove x_n ^ 2 + 1 = 2 * y_n ^ 2 for all n by induction.
  have H (n : ℕ) : x n ^ 2 + 1 = 2 * y n ^ 2 := by
    induction n with
    | zero =>
      simp [hx₀, hy₀]
    | succ n ih =>
      simp [hx, hy, ih]
      linear_combination ih
  -- Since x = 2n + 1, we have n = x div 2.
  let f n := (x n / 2, y n)
  -- We show f is injective since y_n is strictly increasing.
  have hf : Function.Injective f := by
    intro n m h
    simp [f] at h
    exact hymono.injective h.2
  -- It suffices to show that every element of the image of f is a solution to the original equation.
  refine Set.infinite_of_injective_forall_mem hf fun n => ?_
  simp [f, hxpos, hypos]
  -- x_n is odd since x_n ^ 2 + 1 = 2 * y_n ^ 2.
  have hxodd : Odd (x n) := by
    suffices h : Odd (x n ^ 2) from Nat.Odd.of_mul_right h
    suffices h : Even (x n ^ 2 + 1) by simpa [Nat.even_add'] using h
    exact H n ▸ even_two_mul _
  -- So x_n = 2k + 1 for k = x_n / 2.
  have h₁ := Nat.two_mul_div_two_add_one_of_odd hxodd
  set k := x n / 2 with hk
  -- Some simple algebra shows that the result holds.
  suffices 2 * y n ^ 2 = 2 * (2 * k ^ 2 + 2 * k + 1) by simpa using this
  rw [← H n, ← h₁]
  ring