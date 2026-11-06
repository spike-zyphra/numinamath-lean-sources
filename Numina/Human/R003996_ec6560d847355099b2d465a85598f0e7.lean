import Mathlib

open Filter
open scoped Topology

/- 25.30. Let $x_{0}$ and $y_{0}$ be some positive numbers, with $x_{0}>y_{0}, x_{n+1}=\frac{x_{n}+y_{n}}{2}$ and $y_{n+1}=\frac{2 x_{n} y_{n}}{x_{n}+y_{n}}$ for $n \geqslant 0$. Prove that $\lim _{n \rightarrow \infty} x_{n}=\lim _{n \rightarrow \infty} y_{n}=\sqrt{x_{0} y_{0}}$. -/
theorem algebra_228296
    {x y : ℕ → ℝ} (y_pos : y 0 > 0) (x₀_gt_y₀ : x 0 > y 0)
    (hx : ∀ n, x (n + 1) = (x n + y n) / 2)
    (hy : ∀ n, y (n + 1) = 2 * x n * y n / (x n + y n)) :
    Tendsto x atTop (𝓝 √(x 0 * y 0)) ∧ Tendsto y atTop (𝓝 √(x 0 * y 0)) := by
  /- An inequality : for every $n$, from $0 < y_n$ and $y_n < x_n$ we can deduce
    that $x_{n+1} < x_n$ and $y_n < y_{n+1}$. -/
  have ineq' {n : ℕ} : 0 < y n ∧ y n < x n → x (n + 1) < x n ∧ y n < y (n + 1) := by
    rintro ⟨hpos, lt⟩
    simp only [hx, hy]
    constructor
    · rw [div_lt_iff₀ (by simp)]
      linarith
    · rw [lt_div_iff₀]
      · rw [← sub_pos]
        convert_to 0 < y n * (x n - y n)
        · ring
        · exact mul_pos hpos (by linarith)
      · linarith
  /- We could prove inductively that $0 < y_n$ and $y_n < x_n$. -/
  have ineq {n : ℕ} : 0 < y n ∧ y n < x n := by
    induction n with
    | zero => constructor <;> linarith
    | succ n ih =>
      simp only [hx, hy]
      /- Extract the fact that $x_n$ and $y_n$ are positive. -/
      have x_n_pos := ih.1
      have y_n_pos := ih.1.trans ih.2
      constructor
      · positivity
      · /- After denominators cancelled, the equality becomes $0 < (x_n - y_n)^2$,
          which proof uses the induction hypothesis $y_n < x_n$. -/
        rw [div_lt_div_iff₀ (by positivity) (by simp), ← sub_pos]
        convert_to 0 < (x n - y n) ^ 2
        · ring
        · have : 0 < x n - y n := by linarith
          positivity
  /- We can easily deduce that $0 < x_n$ and $0 < y_n$. -/
  have x_pos {n : ℕ} : 0 < x n := ineq.1.trans ineq.2
  have y_pos {n : ℕ} : 0 < y n := ineq.1
  /- The sequence $x$ is monotone decreasing and has a lower bound. -/
  have anti_x : Antitone x :=
    antitone_nat_of_succ_le fun _ => le_of_lt (ineq' ineq).1
  have bounded_x : BddBelow (Set.range x) := by
    use 0
    simpa [lowerBounds] using fun _ => le_of_lt x_pos
  /- The sequence $x$ is monotone increasing and has a upper bound. -/
  have mono_y : Monotone y :=
    monotone_nat_of_le_succ fun _ => le_of_lt (ineq' ineq).2
  have bounded_y : BddAbove (Set.range y) := by
    use x 0
    simpa [upperBounds] using fun _ => (le_of_lt ineq.2).trans (anti_x (by simp))
  /- So the sequence $x$ and $y$ both have limits, we denote these limits as $X$ and $Y$. -/
  obtain ⟨X, hX⟩ := Real.tendsto_of_bddBelow_antitone bounded_x anti_x
  obtain ⟨Y, hY⟩ := Real.tendsto_of_bddAbove_monotone bounded_y mono_y
  clear ineq ineq' anti_x bounded_x mono_y bounded_y
  /- Since $X = \frac{X + Y}{2}$, we have $X = Y$. -/
  have X_eq_Y : X = Y := by
    suffices X = (X + Y) / 2 by linarith
    apply tendsto_nhds_unique_of_eventuallyEq
      (f := x ∘ (· + 1)) (g := fun n => (x n + y n) / 2) (l := atTop)
    · exact .comp hX (tendsto_add_atTop_nat _)
    · exact .div (.add hX hY) (by simp) (by simp)
    · exact .of_eq (funext hx)
  /- We can prove $XY = x_0y_0$ from $x_ny_n = x_0y_0$. -/
  have mul_eq : X * Y = x 0 * y 0 := by
    apply tendsto_nhds_unique_of_eventuallyEq
      (f := fun n => x n * y n) (g := fun _ => x 0 * y 0) (l := atTop)
    · exact .mul hX hY
    · simp
    · refine .of_eq (funext fun n => ?_)
      /- We prove inductively, $x_{n+1}y_{n+1} = x_0y_0$. -/
      induction n with
      | zero => rfl
      | succ n ih =>
        simp only [hx, hy, ← ih]
        have : x n + y n ≠ 0 := ne_of_gt (add_pos x_pos y_pos)
        field_simp
        ring
  /- Now from the positivity of $X$ we could deduce that the limit is $\sqrt{x_0y_0}$. -/
  cases X_eq_Y
  rw [← Real.sqrt_eq_iff_mul_self_eq_of_pos] at mul_eq
  · cases mul_eq
    exact ⟨hX, hY⟩
  · apply lt_of_le_of_ne
    · exact ge_of_tendsto hX (.of_forall fun n => le_of_lt x_pos)
    · intro eq
      simp [← eq, x_pos, y_pos, ne_of_gt] at mul_eq
