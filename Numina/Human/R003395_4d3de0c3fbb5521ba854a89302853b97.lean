import Mathlib

open Real

/- 
Problem № 6 (15 points)

A body is thrown vertically upwards from a high balcony. The dependence of the modulus of the body's acceleration on time is shown in the graph. Using this dependence, estimate the terminal velocity of the body. The acceleration due to gravity $ g = 10 \, \text{m} / \text{s}^2 $.

![](https://cdn.mathpix.com/cropped/2024_05_06_dde97d69ac546735bb46g-08.jpg?height=917&width=1285&top_left_y=958&top_left_x=434)

Answer: $ 25 \, \text{m} / \text{s} $

-/
theorem calculus_175747
  {v : ℝ → ℝ} -- the velocity function
  {m k t : ℝ} -- m is mass, k is drag coefficient, t is time
  -- Graph shows a continuous function for acceleration
  (continuous_on : ContinuousOn (derivWithin v (Set.Icc 0 2)) (Set.uIcc 0 2))
  -- Graph shows a differentiable function between 0 and 2
  (hderiv : ∀ t, HasDerivAt v (derivWithin v (Set.Icc 0 2) t) t)
  -- Mass and drag coefficient are positive
  (m_pos : 0 < m) (k_pos : 0 < k)
  -- Graph shows an acceleration at t = 0 of 20
  (initial_a : derivWithin v (Set.Icc 0 2) 0 = 20)
  -- Graph shows an acceleration at t = 2 of 10
  (zero_v : derivWithin v (Set.Icc 0 2) 2 = 10)
  -- Problem states that the ball is thrown upwards
  (initial_sign : SignType.sign (v 0) = -1)
  -- The slope is constant from t = 0 to t = 2 from the graph,
  -- so there exists constants b and c which describe the line.
  (linear_a : ∃ b c, derivWithin v (Set.Icc 0 2) = λ t => b*t + c)
  -- Newton's second law with air resistance proportional
  -- to the square of velocity
  (net_force : ∀ t, m*(derivWithin v (Set.Icc 0 2) t) = m*10 - SignType.sign (v t) * k*(v t) ^ 2)
  -- When the velocity is constant, it is the terminal velocity
  (terminal_v : deriv v t = 0)
  -- The area under the curve from 0 to 2 in the graph is 30
  : v t = 30
    := by
  -- The velocity at 2 can be determined because the acceleration is 10
  -- (from the graph) which is equal to g.
  have v2 : v 2 = 0 := by
    specialize net_force 2
    -- Apply the fact that the acceleration equals g
    rw [zero_v] at net_force
    -- Move 10m to the other side
    apply congrArg (· - m * 10) at net_force
    simp [or_comm] at net_force
    -- Eliminate impossible cases (because k is non-zero)
    rcases net_force with (_ | _ | sign_0)
    · assumption
    · exact (k_pos.ne.symm (by assumption)).elim
    · simp [SignType.sign] at sign_0
      split_ifs at sign_0 <;> simp_all
      · apply le_antisymm <;> assumption

  -- The velocity at 0 can be determined as well from Newton's second law
  have v0 : v 0 = -√(10 * m / k) := by
    specialize net_force 0
    -- Apply known variables
    simp [initial_sign, initial_a] at net_force ⊢
    -- Move 10m to the other side
    apply congrArg (· - m * 10) at net_force
    ring_nf at net_force
    -- Move k to the other side
    have v_sq : v 0 ^ 2 = m * 10 / k := by
      -- Divide both sides by k
      apply congrArg (· / k) at net_force
      -- Simplify only on the right side
      conv_rhs at net_force => tactic => field_simp
      exact net_force.symm
    -- Square root both sides
    apply congrArg sqrt at v_sq
    -- Apply the property of a square of an absolute
    rw [sqrt_sq_eq_abs] at v_sq
    -- Multiply both sides by negative oneg
    apply congrArg (· * -1) at v_sq
    -- Rewrite -1 in terms of sign, then apply the initial negative velocity
    rw [<- abs_mul_sign (v 0), initial_sign]
    simp [v_sq, mul_comm]

  -- We can find b = -5, c = 20 and specialize linear_a
  replace linear_a : derivWithin v (Set.Icc 0 2) = λ t => -5*t + 20 := by
    obtain ⟨ b, c, deriv_eq ⟩ := linear_a
    -- Compare the linear function to the goal
    rw [deriv_eq]
    -- Find c
    have h₁ := by simpa [deriv_eq] using initial_a
    subst c
    -- Find an equation for b
    have h₂ := by simpa [deriv_eq] using zero_v
    have : b = -5 := by
      apply congrArg (· - 20) at h₂
      linear_combination h₂ / 2
    subst b
    rfl

  -- Integrate the acceleration from 0 to 2
  have integral : v 2 - v 0 = ∫ (t : ℝ) in (0)..2, -5 * t + 20 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (λ x a => hderiv x)
      (ContinuousOn.intervalIntegrable continuous_on)
    rw [<- linear_a, this]

  -- Calculate the area under the curve, by evaluating the integral
  have : v 2 - v 0 = 30 := by
    rw [integral]
    -- Apply the associative property of integration
    rw [intervalIntegral.integral_add ?_ (by simp)]
    norm_num
    -- Extract the constant of 5
    have : ∫ (x : ℝ) in (0)..2, 5 * x = 5 * ∫ (x : ℝ) in (0)..2, x := by
      exact intervalIntegral.integral_const_mul 5 id
    rw [this]
    -- Evaluate
    norm_num
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      exact continuousOn_id' (Set.uIcc 0 2)

  -- Calculate the ratio of m to k from system of equations for v0
  have m_div_k : m / k = 90 := by
    rw [v0, v2] at this
    norm_num at this
    -- Square both sides
    apply congrArg (· ^ 2) at this
    rw [sq_sqrt] at this
    -- Simplify
    linear_combination this / 10
    · positivity

  -- Show that the net force equation holds for all t
  replace net_force : deriv v t = 10 - ((SignType.sign (v t)) * (k / m) * v t ^ 2)
      := by
    specialize net_force t
    -- The derivative is equal because we assumed differentiability between
    -- 0 to 2
    rw [deriv_eq hderiv]
    -- Simplify
    apply congrArg (· / m) at net_force
    simp [sub_div, mul_div_cancel_left₀ _ m_pos.ne.symm] at net_force
    linear_combination net_force

  -- Simplify m/k from the net force equation
  replace net_force : (SignType.sign (v t)) * (v t ^ 2) = 30^2 := by
    apply congrArg (m * 10 - ·) at net_force
    -- Invert m/k
    have : k / m = 1 / 90 := by
      apply congrArg (1 / ·) at m_div_k
      simpa using m_div_k

    simp [this] at net_force
    apply congrArg (· * 90) at net_force
    -- Apply the assumption that the terminal velocity is when the derivative
    -- is 0
    field_simp [terminal_v] at net_force
    linear_combination net_force

  -- Show the sign of the terminal velocity is positive (downwards) by
  -- contradiction
  have sign_vt_1 : SignType.sign (v t) = 1 := by
    -- Show the square is nonneg
    have : 0 ≤ (v t)^2 := sq_nonneg (v t)
    -- Show the velocity cannot be 0
    have : 0 ≠ (v t) := by
      by_contra eq
      -- Rewrite 0 = v t to get a contradiction at net_force
      norm_num [<- eq] at net_force
    -- Calculate each case of the sign
    rw [sign_apply]
    split_ifs with neg pos <;> try norm_num [*] at *
    · linarith
    · have := (LE.le.antisymm neg pos).symm
      contradiction

  -- A sign of 1 is positive
  have pos_v : 0 < v t := by
      exact sign_eq_one_iff.mp sign_vt_1
  -- Square root both sides
  apply congrArg (sqrt) at net_force
  -- Simplify
  simpa [sign_vt_1, sqrt_sq pos_v.le] using net_force