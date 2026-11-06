import Mathlib

/- 15. If $\alpha$ is a real root of the equation $x^{5}-x^{3}+x-2=0$, find the value of $\left\lfloor\alpha^{6}\right\rfloor$, where $\lfloor x\rfloor$ is the least positive integer not exceeding $x$. -/
theorem algebra_99437 {α : ℝ} (h : α^5 - α^3 + α - 2 = 0) : ⌊α^6⌋ = 3 := by
  -- Let f(x) = x^5 - x^3 + x - 2. First we find the derivative of f and note it is
  -- always positive, so f is strictly increasing.
  let f : ℝ → ℝ := fun x ↦ x^5 - x^3 + x - 2

  have (x : ℝ) : deriv f x = 5 * x^4 - 3 * x^2 + 1 := by
    rw [deriv_sub, deriv_add, deriv_sub]; simp
    all_goals simp

  have f_mono : StrictMono f := by
    apply strictMono_of_deriv_pos
    intro x
    rw [this]
    rw [show 5 * x ^ 4 - 3 * x ^ 2 + 1 = 5 * (x^2 - 3/10)^2 + 55/100 by ring_nf]
    refine add_pos_of_nonneg_of_pos ?_ (by simp)
    simp
    exact sq_nonneg _

  -- From this we can find bounds for α.
  have : 1 < α := by
    rw [← StrictMono.lt_iff_lt f_mono]
    simp [f, h]

  have : α < 2 := by
    rw [← StrictMono.lt_iff_lt f_mono]
    simp [f, h]
    norm_num

  have α_nonzero : α ≠ 0 := by linarith

  -- Next we need to find bounds for α^6. Using f(α) = 0, we can
  -- simplify this to the following:
  have α_pow_6 : α^6 = α * 2 - 1 + α⁻¹ * 2 := by
    have eq1 : α^5 = α^3 - α + 2 := by
      rw [← sub_eq_zero]
      ring_nf
      ring_nf at h
      exact h
    have eq2 : α^6 = α^4 - α^2 + 2 * α := by
      apply_fun fun x ↦ x * α at eq1
      ring_nf
      ring_nf at eq1
      exact eq1
    have eq3 : α^4 = α^2 - 1 + 2 * α ⁻¹ := by
      apply mul_left_cancel₀ α_nonzero
      ring_nf
      rw [eq1]
      simp [α_nonzero]
      ring
    rw [eq2, eq3]
    ring

  -- Let g(x) = x * 2 - 1 + x⁻¹ * 2. We can find the derivative of g too
  -- and show it is increasing on 1 ≤ x ≤ 2.
  let g : ℝ → ℝ := fun x ↦ x * 2 - 1 + x⁻¹ * 2

  have (x : ℝ) (hx : x ≠ 0) : deriv g x = 2 - 2/x^2 := by
    rw [deriv_add, deriv_sub]; simp; ring
    any_goals simp
    apply DifferentiableAt.mul_const
    apply DifferentiableAt.inv _ hx
    simp

  have g_mono : StrictMonoOn g (Set.Icc 1 2) := by
    simp [g]
    apply strictMonoOn_of_deriv_pos
    . exact convex_Icc _ _
    . apply ContinuousOn.add (ContinuousOn.sub (ContinuousOn.mul continuousOn_id continuousOn_const) continuousOn_const)
      refine ContinuousOn.mul ?_ continuousOn_const
      apply ContinuousOn.inv₀ continuousOn_id
      intro x
      simp
      intro hx1 hx2
      linarith
    . simp
      intro x hx1 hx2
      rw [this x (by linarith)]
      simp
      rw [div_lt_iff₀' (sq_pos_of_pos (by linarith))]
      simp
      rw [lt_abs]
      simp [hx1]

  -- From this we can get bounds for α^6.
  have : 3 ≤ α^6 := by
    rw [show 3 = g 1 by simp [g]; norm_num]
    rw [show α^6 = g α by simp [g, α_pow_6]]
    rw [StrictMonoOn.le_iff_le g_mono]
    . linarith
    . simp
    . and_intros
      . linarith
      . linarith
  have : 3 ≤ ⌊α^6⌋ := by
    rw [Int.le_floor]
    exact this

  have : α^6 < 4 := by
    rw [show 4 = g 2 by simp [g]; norm_num]
    rw [show α^6 = g α by simp [g, α_pow_6]]
    rw [StrictMonoOn.lt_iff_lt g_mono]
    . linarith
    . and_intros
      . linarith
      . linarith
    . simp
  have : ⌊α^6⌋ < 4 := by
    rw [Int.floor_lt]
    exact this

  -- Finally we can conclude that ⌊α^6⌋ = 3.
  linarith