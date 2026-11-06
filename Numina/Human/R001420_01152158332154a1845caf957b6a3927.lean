import Mathlib

/- 12. (GDR 3) ${ }^{\mathrm{IMO} 3}$ To each vertex $P_{i}(i=1, \ldots, 5)$ of a pentagon an integer $x_{i}$ is assigned, the sum $s=\sum x_{i}$ being positive. The following operation is allowed, provided at least one of the $x_{i}$ 's is negative: Choose a negative $x_{i}$, replace it by $-x_{i}$, and add the former value of $x_{i}$ to the integers assigned to the two neighboring vertices of $P_{i}$ (the remaining two integers are left unchanged). This operation is to be performed repeatedly until all negative integers disappear. Decide whether this procedure must eventually terminate. -/
theorem combinatorics_24012 (x : Fin 5 → ℤ)
    (h_sum : 0 < ∑ i : Fin 5, x i) :
    let R (y x : Fin 5 → ℤ) : Prop := ∃ i : Fin 5, x i < 0 ∧
      y i = - x i ∧
      y (i + 1) = x (i + 1) + x i ∧
      y (i - 1) = x (i - 1) + x i ∧
      y (i + 2) = x (i + 2) ∧
      y (i - 2) = x (i - 2);
    Acc R x := by
  intro R
  -- We define $f\left(x_{1}, \ldots, x_{5}\right)=\sum_{i=1}^{5}\left(x_{i+1}-x_{i-1}\right)^{2}\left(x_{0}=x_{5}, x_{6}=x_{1}\right)$.
  -- We need to "lift" $f$ from $\mathbb{Z}$ to $\mathbb{N}$, because we are going to use its well-foundedness.
  let f' (x : Fin 5 → ℤ) : ℤ := ∑ i : Fin 5, (x (i + 1) - x (i - 1))^2
  obtain ⟨f, hf'⟩ : ∃ f : (Fin 5 → ℤ) → ℕ, ∀ x, f' x = f x := by
    have : ∀ x, 0 ≤ f' x := by
      intro x
      simp [f']
      positivity
    use fun x ↦ (Int.eq_ofNat_of_zero_le (this x)).choose
    intro x
    simp
    generalize_proofs h
    exact h.choose_spec
  -- Now we use induction showing that $f$ strictly decreases after each step.
  induction' h : f x using Nat.strong_induction_on with d ih generalizing x
  constructor
  intro y hRyx
  simp [R] at hRyx
  obtain ⟨i, h_neg, h_eq1, h_eq2, h_eq3, h_eq4, h_eq5⟩ := hRyx
  have h_cast1 : (-1 : Fin 5) = 4 := rfl
  have h_cast2 : (-2 : Fin 5) = 3 := rfl
  have h_cast3 : (-3 : Fin 5) = 2 := rfl
  have h_cast4 : (-4 : Fin 5) = 1 := rfl
  have h_cast5 : (-5 : Fin 5) = 0 := rfl
  have h_sum' (z : Fin 5 → ℤ) : ∑ i : Fin 5, z i = z i + z (i + 1) + z (i - 1) + z (i + 2) + z (i - 2) := by
    rw [Fin.sum_univ_five]
    fin_cases i <;> (simp [h_cast1, h_cast2, h_cast3, h_cast4, h_cast5]; ring)
  -- We need to show that $f(Y) < f(X)$ and the sum of the $y_i$ is positive.
  apply ih (f y)
  · rw [← h]
    -- The difference $$ \begin{aligned} f(Y)-f(X)= & \left(x_{2}+x_{3}-x_{5}\right)^{2}+\left(x_{1}+x_{3}\right)^{2}+\left(x_{2}-x_{4}\right)^{2} \ & +\left(x_{3}+x_{5}\right)^{2}+\left(x_{1}-x_{3}-x_{4}\right)^{2}-\left(x_{2}-x_{5}\right)^{2} \ & -\left(x_{3}-x_{1}\right)^{2}-\left(x_{4}-x_{2}\right)^{2}-\left(x_{5}-x_{3}\right)^{2}-\left(x_{1}-x_{4}\right)^{2} \ = & 2 x_{3}\left(x_{1}+x_{2}+x_{3}+x_{4}+x_{5}\right)=2 x_{3} S<0 \end{aligned} $$ is negative.
    have : f' y - f' x = 2 * x i * (x i + x (i + 1) + x (i - 1) + x (i + 2) + x (i - 2)) := by
      simp [f', h_sum']
      ring_nf at h_eq1 h_eq2 h_eq3 h_eq4 h_eq5 ⊢
      have h_cast6 : 3 + i = -2 + i := rfl
      have h_cast7 : -3 + i = 2 + i := rfl
      simp [h_cast6, h_cast7, h_eq1, h_eq2, h_eq3, h_eq4, h_eq5]
      ring_nf
    -- So $f(Y) < f(X)$.
    rw [← h_sum' x] at this
    have : f' y < f' x := by
      nlinarith
    rw [hf', hf'] at this
    rwa [← Int.ofNat_lt]
  -- The sum of the $y_i$ is equal to the sum of the $x_i$, so it is positive.
  · calc
      _ < _ := h_sum
      _ = x i + x (i + 1) + x (i - 1) + x (i + 2) + x (i - 2) := by rw [h_sum']
      _ = y i + y (i + 1) + y (i - 1) + y (i + 2) + y (i - 2) := by simp [*]; ring
      _ = _ := by rw [h_sum']
  · rfl
