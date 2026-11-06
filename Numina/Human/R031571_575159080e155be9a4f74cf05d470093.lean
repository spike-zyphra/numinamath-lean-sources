import Mathlib

/- Given the function $f(x)=e^{x}(ax-a+2)$ has a local minimum at $-2$. Find the equation of the tangent line to the function $f(x)$ at $x=0$. Let $g(x)=mf(x)-x(x+4)$, for all $x\in [-2,+\infty)$, if $g(x)\geqslant 2$ always holds, find the range of real number $m$. -/
theorem algebra_9374 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => Real.exp x * (a * x - a + 2)) (h : Differentiable ℝ f) (hlocalmin: IsLocalMin f (-2)) :(∀ (k b:ℝ), (k*0+b = f 0 ∧ deriv f 0 = k) → k = 2 ∧ b = 1) ∧ (∀m:ℝ, (∀ x ∈ Set.Ici (-2), m * (f x) - x * (x + 4) ≥ 2) ↔ (m ∈ Set.Icc 2 (2 * Real.exp 2)) ) := by
-- The problem has two questions.
-- one deal with f(x) = e^x(ax-a+2), and the other with g(x) = mf(x)-x(x+4)
-- before answer these questions, in fact, we can determine a=1.
-- so the first part of the answer, is to solve a=1.
-- and the second part, find the equation of tangent line to f(x) at x=0.
-- the third part, is to prove for all x ≥ 2, if g(x) ≥ 2 always holds, then 2 ≤ m ≤ 2e^2
-- the third part involves finding minimum function value by calculating its derivative. Thereby, we have to prove the funciton is differentiable and continuous.
have aeq: a = 1 := by
  -- first part. determine a.
  have derivf: deriv f (-2) = deriv Real.exp (-2) * (a*(-2)-a+2) + Real.exp (-2) * deriv (fun x => (a*x-a+2)) (-2) := by
    let f1 := Real.exp
    have f1_def: f1 = Real.exp := rfl
    let f2 := fun x => (a*x-a+2)
    have f2_def: f2 = fun x => (a*x-a+2) := rfl
    have ht1: deriv f (-2) = deriv (fun x => f1 x * f2 x) (-2) := by
      exact congrFun (congrArg deriv hf) (-2)
    have ht2: f = fun x => f1 x * f2 x := hf
    have ht3: Differentiable ℝ (fun x => f1 x * f2 x) := by
      rwa [ht2] at h
    have df1: deriv f1 (-2) = f1 (-2) := by
      rw [f1_def]; simp
    have df2: deriv f2 (-2) = a := by
      rw [f2_def]
      simp
      have: deriv (fun y => a * y - a) (-2) = deriv (fun y => a*y) (-2) := deriv_sub_const a
      rw [this]
      have: deriv (fun y => a * y) (-2) = deriv (fun y => a * id y) (-2) := by simp
      rw [this]
      have: deriv (fun y => a * y) (-2:ℝ) = a * deriv id (-2:ℝ) := by
        have hid: DifferentiableAt ℝ (fun y => y) (-2:ℝ) := by apply differentiableAt_id
        apply deriv_const_mul
        apply hid
      simp [this]
    have ht4: DifferentiableAt ℝ f1 (-2) := by
      exact Real.differentiableAt_exp
    have ht5: DifferentiableAt ℝ f2 (-2) := by
      by_cases ha: a = 0
      rw [ha] at hf
      simp_all
      rw [← df2] at ha
      push_neg at ha
      exact differentiableAt_of_deriv_ne_zero ha
    have ht6: deriv (fun x => f1 x * f2 x) (-2) = deriv f1 (-2) * f2 (-2) + f1 (-2) * deriv f2 (-2) := deriv_mul ht4 ht5
    rw [ht1, ht6]
  -- since f(x) has a local minimum at -2, f'(-2) = 0.
  have h': deriv f (-2) = 0 := IsLocalMin.deriv_eq_zero hlocalmin
  rw [h'] at derivf
  simp at derivf
  have: deriv (fun y => a * y - a) (-2) = a := by
    have: deriv (fun y => a * y - a) (-2) = deriv (fun y => a*y) (-2) := by exact deriv_sub_const a
    rw [this]
    have: deriv (fun y => a * y) (-2) = deriv (fun y => a * id y) (-2) := by simp
    rw [this]
    have: deriv (fun y => a * y) (-2:ℝ) = a * deriv id (-2:ℝ) := by
        have hid: DifferentiableAt ℝ (fun y => y) (-2:ℝ) := by apply differentiableAt_id
        apply deriv_const_mul
        apply hid
    simp [this]
  rw [this] at derivf
  have h1: Real.exp (-2) * (-(a * 2) - a + 2) + Real.exp (-2) * a = Real.exp (-2) * (-(a*2)-a+2+a) := by ring
  rw [h1] at derivf
  have h2: (-(a * 2) - a + 2 + a) = 0 := by
    have: 0 ≠ Real.exp (-2) := Ne.symm (Real.exp_ne_zero (-2))
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero (id (Ne.symm this)) (id (Eq.symm derivf))
  linarith [h2]
rw [aeq] at hf
simp_all only [aeq, sub_add, one_mul]
-- second part. find the tangent line equation. we can prove it is y=2x+1
have tangent_line: (∀ (k b : ℝ), k * 0 + b = Real.exp 0 * (0 - (1 - 2)) ∧ deriv (fun x => Real.exp x * (x - (1 - 2))) 0 = k → k = 2 ∧ b = 1) := by
  intro k b heq
  rcases heq with ⟨eq1, eq2⟩
  simp at eq1
  have beq: b = 1 := by linarith [eq1]
  have ht1: deriv (fun x => Real.exp x * (x - (1 - 2))) 0 = deriv (fun x => Real.exp x * (x+1)) 0 := by
    congr
    funext x
    ring
  have ht2: deriv (fun x => Real.exp x * (x+1)) 0 = deriv Real.exp 0 * (fun x => (x+1)) 0 + Real.exp 0 * deriv (fun x => (x+1)) 0 := by
    have hd1: DifferentiableAt ℝ Real.exp 0 := by
      exact Real.differentiableAt_exp
    have hd2: DifferentiableAt ℝ (fun y => y + (1:ℝ)) 0 := by
      have: DifferentiableAt ℝ (fun y => y) (0:ℝ) := by exact differentiableAt_id'
      exact DifferentiableAt.add_const this 1
    exact deriv_mul hd1 hd2
  rw [ht1, ht2] at eq2
  simp at eq2
  have keq: k = 2 := by linarith [eq2]
  exact ⟨keq, beq⟩
-- third part. find the range of real number m
have range_m: ∀m:ℝ,(∀x:ℝ, x ∈ Set.Ici (-2) → (m * (Real.exp x * (x - (1 - 2))) - x * (x + 4) ≥ 2)) ↔ (m ∈ Set.Icc 2 (2 * Real.exp 2)) := by
  intro m
  -- the given condition is m*f1(x)+f2(x) >=2.
  -- let g(x)=m*f1(x)+f2(x).
  -- calculate g'(x) and find the minimum
  let f1 := fun y => (Real.exp y * (y - (1 - 2)))
  have f1_def: f1 = fun y => (Real.exp y * (y-(1-2))) := rfl
  have f1_def': f1 = (fun y => Real.exp y * (y+1)) := by
      rw [f1_def]
      ext y
      ring
  let f2 := fun (y:ℝ) => -y*(y+4)
  have f2_def : f2 = fun y => -y*(y+4) := rfl
  have f2_def': f2 = fun y => -y^2-4*y := by
    rw [f2_def]
    funext y
    ring
  let g := fun y => m * f1 y - y * (y+4)
  have g_def : g = fun y => m * f1 y - y * (y+4) := rfl
  have g_def': g = fun y => m * f1 y + f2 y := by
    rw [g_def, f2_def]
    funext y
    ring
  have f1_deriv: deriv f1 = fun y => Real.exp y * (y+2) := by
    rw [f1_def']
    funext y
    have ht1: deriv (fun y => Real.exp y * (y + 1)) y = deriv Real.exp y * (fun y => (y+1)) y + Real.exp y * deriv (fun y => (y+1)) y := by
      have hd1: DifferentiableAt ℝ Real.exp y := by
        exact Real.differentiableAt_exp
      have hd2: DifferentiableAt ℝ (fun y => y + 1) y := by
        have: DifferentiableAt ℝ (fun y => y) y := by
          exact differentiableAt_id'
        exact DifferentiableAt.add_const this 1
      exact deriv_mul hd1 hd2
    have ht2: deriv Real.exp y = Real.exp y := by simp
    have ht3: deriv (fun y => y+1) y = 1 := by simp
    rw [ht1, ht2, ht3]
    simp
    ring
  have f2_deriv: deriv f2 = fun y => -2*y-4 := by
    rw [f2_def']
    funext y
    have h1: deriv (fun y => -y^2 - 4*y) y = deriv (fun y => -y^2) y - deriv (fun y => 4*y) y := by
      have ht1: DifferentiableAt ℝ (fun y => -y ^ 2) y := by
        have: DifferentiableAt ℝ (fun y => y^2) y := by
          exact differentiableAt_pow 2
        exact differentiableAt_neg_iff.mpr this
      have ht2: DifferentiableAt ℝ (fun (y:ℝ) => 4*y) y := by
        have: DifferentiableAt ℝ (fun y => (y:ℝ)) y := by
          exact differentiableAt_id'
        apply DifferentiableAt.const_mul this
      exact deriv_sub ht1 ht2
    have h2: deriv (fun y => -y^2) y = -2*y := by simp
    have h3: deriv (fun y => 4*y) y = 4 := by
      have ht1: deriv (fun y => (y:ℝ)) y = 1 := by simp
      have ht2: deriv (fun y => 4*y) y= 4 * deriv (fun y => y) y:= by
        exact deriv_const_mul_field 4
      rw [ht2, ht1]
      simp
    rw [h1, h2, h3]
  have g_deriv: deriv g = fun y => (y+2)*(m * Real.exp y - 2) := by
    rw [g_def']
    funext y
    have h1: deriv (fun y => m * f1 y + f2 y) y = m * deriv f1 y + deriv f2 y := by
      have ht1: deriv (fun y => m * f1 y) y = m * deriv f1 y := by simp
      have ht2: deriv (fun y => m* f1 y + f2 y) y = deriv (fun y => m * f1 y) y + deriv f2 y := by
        have hdif1: DifferentiableAt ℝ (fun y => m * f1 y) y := by
          have: DifferentiableAt ℝ f1 y := by
            have hd1: DifferentiableAt ℝ Real.exp y := by
              exact Real.differentiableAt_exp
            have hd2: DifferentiableAt ℝ (fun y => y + 1) y := by
              have: DifferentiableAt ℝ (fun y => y) y := by
                exact differentiableAt_id'
              exact DifferentiableAt.add_const this 1
            rw [f1_def']
            exact DifferentiableAt.mul hd1 hd2
          exact DifferentiableAt.const_mul (h y) m
        have hdif2: DifferentiableAt ℝ f2 y := by
          rw [f2_def']
          have: DifferentiableAt ℝ (fun y => 4*y) y:= by
            have: DifferentiableAt ℝ (fun y => (y:ℝ)) y := by
              exact differentiableAt_id'
            apply DifferentiableAt.const_mul this 4
          simp [this]
        apply deriv_add hdif1 hdif2
      rw [ht2, ht1]
    rw [h1, f1_deriv, f2_deriv]
    simp
    ring
  constructor
  -- the proof has two direction.
  -- in the mp direction, we know the minimum of function, and decide range of m. we can avoid derivative here.
  -- However, since the mpr direction needs derivative. so related calculation is given.
  intro ineq
  have m_upper: m ≤ 2 * (Real.exp 2) := by
    by_contra! hc
    have h1: g (-2:ℝ) = 4 - m * (Real.exp (-2)) := by
      rw [g_def, f1_def']
      simp
      ring
    have h2: m * (Real.exp (-2)) > 2 := by
      have ht1: m / (Real.exp 2) > 2 := by
        have h11: m > 2 * Real.exp 2 := hc
        have h22: 0 < Real.exp 2 := Real.exp_pos 2
        exact (lt_div_iff h22).mpr hc
      have ht2: m / Real.exp 2 = m * (Real.exp (-2)) := by
        field_simp
        rw [mul_assoc]
        have: Real.exp (-2) * Real.exp 2 = 1 := by
          have: Real.exp (-2) = (Real.exp 2)⁻¹ := Real.exp_neg 2
          simp [this]
        simp [this]
      rwa [ht2] at ht1
    rcases ineq (-2) with h3
    have h4: ¬ m * Real.exp (-2) > 2 := by
      have ht1: m * (Real.exp (-2) * (-2 - (1 - 2))) - -2 * (-2 + 4) ≥ 2 := by
        have: (-2:ℝ) ∈ Set.Ici (-2) := Set.left_mem_Ici
        apply h3 this
      simp at ht1
      norm_num at ht1
      have: m * Real.exp (-2) ≤ 2 := by linarith [ht1]
      linarith [this]
    contradiction
  have m_lower: 2 ≤ m := by
    by_cases mpos: m ≤ 0
    -- any enough big x is OK. here we choose 4.
    rcases ineq (4:ℝ) with h1
    have h1: m * (Real.exp 4 * (4 - (1 - 2))) - 4 * (4 + 4) ≥ 2 := by
      have: (4:ℝ) ∈ Set.Ici (-2) := by
        simp
        norm_num
      apply h1 this
    simp at h1
    have: m * (Real.exp 4 * (4 - (1 - 2))) - 4 * (4 + 4) = m*(5* Real.exp 4) - 32 := by ring
    rw [this] at h1
    have ht: 2+32 ≤ m* (5*Real.exp 4):= le_sub_iff_add_le.mp h1
    norm_num at ht
    exfalso
    have h2: 0 < 5*Real.exp 4 := by
      have: 0 < Real.exp 4 := Real.exp_pos 4
      simp [this]
    have h3: 0 < m := by
      have htt1: 0 < (34:ℝ) := by norm_num
      have htt2: 0 < m*(5*Real.exp 4) := by linarith
      exact (pos_iff_pos_of_mul_pos htt2).mpr h2
    linarith [h3, mpos]
    push_neg at mpos
    -- now m>0
    -- in the mpr direction, we will calculate g'(x), and show g'(x) = 0 when x = -2 and ln(2/m). if m=2, then g(-2) is minimu. otherwise, g (ln(2/m)) is minimum.
    -- so we use ln(2/m) here.
    have mnez: 0 ≠ m := by linarith [mpos]
    have m2pos: 0 < 2/m := by
      have: 0 < (2:ℝ) := by norm_num
      exact div_pos this mpos
    have hlnm: (-2:ℝ) ≤ Real.log (2/m) := by
      have h1: 2/m ≥ Real.exp (-2) := by
        have ht1: 2 * m ≤ 2 * (2*Real.exp 2) := by
          linarith [m_upper]
        have ht2: 2 * m / m ≤ 2 * (2*Real.exp 2) / m := by
          exact (div_le_div_right mpos).mpr ht1
        rw [mul_div_assoc] at ht2
        have: m/m = 1 := by
          exact (div_eq_one_iff_eq (id (Ne.symm mnez))).mpr rfl
        rw [this] at ht2
        simp at ht2
        have:  2 * (2 * Real.exp 2) / m = (2/m) * (2*Real.exp 2) := by ring
        rw [this] at ht2
        have ht3: 2/m * (2*Real.exp 2) ≥ 2 := ht2
        have ht4: 2/m * (2*Real.exp 2) /(2*Real.exp 2) ≥ 2 / (2*Real.exp 2) := by
          have: 0 < 2 * Real.exp 2 := gt_of_ge_of_gt m_upper mpos
          exact (div_le_div_right this).mpr ht2
        simp at ht4
        have: 2 / (2 * Real.exp 2) = Real.exp (-2) := by
          have: 2/(2*Real.exp 2) = (2/2)/(Real.exp 2) := by ring
          rw [this]
          simp
          exact Eq.symm (Real.exp_neg 2)
        rwa [this] at ht4
      have: (-2:ℝ) = Real.log (Real.exp (-2)) := by
        exact Eq.symm (Real.log_exp (-2))
      rw [this]
      have h3: 0 < Real.exp (-2) := Real.exp_pos (-2)
      exact (Real.log_le_log_iff h3 m2pos).mpr h1
    rcases ineq (Real.log (2/m)) with ineq2'
    have ineq2: m * (Real.exp (Real.log (2 / m)) * (Real.log (2 / m) - (1 - 2))) - Real.log (2 / m) * (Real.log (2 / m) + 4) ≥ 2 := by
      apply ineq2' hlnm
    have: m * (Real.exp (Real.log (2 / m)) * (Real.log (2 / m) - (1 - 2))) - Real.log (2 / m) * (Real.log (2 / m) + 4) = 2 * (Real.log (2/m)+1) - (Real.log (2/m) * (Real.log (2/m) + 4)) := by
      have: Real.exp (Real.log (2/m)) = 2/m := by
        apply Real.exp_log m2pos
      rw [this]
      have ht1: (Real.log (2 / m) - (1 - 2)) = Real.log (2/m) + 1 := by
        ring
      rw [ht1]
      simp
      rw [← mul_assoc]
      have ht2: m * (2/m) = 2 := by
        exact mul_div_cancel₀ 2 (id (Ne.symm mnez))
      rw [ht2]
    rw [this] at ineq2
    have ineq3': -Real.log (2/m) * (Real.log (2/m) + 2) ≥ 0 := by
      have: 2 * (Real.log (2 / m) + 1) - Real.log (2 / m) * (Real.log (2 / m) + 4) = -Real.log (2/m) * (Real.log (2/m) + 2) + 2 := by
        ring
      rw [this] at ineq2
      exact nonneg_of_le_add_left ineq2
    have ineq3:  Real.log (2/m) * (Real.log (2/m)+2) ≤ 0:= by
      have: -Real.log (2/m) * (Real.log (2 / m) + 2) = -(Real.log (2/m) * (Real.log (2/m)+2)) := by ring
      rw [this] at ineq3'
      exact neg_nonneg.mp ineq3'
    have h1: 0 ≤ (Real.log (2 / m) + 2) := neg_le_iff_add_nonneg.mp hlnm
    by_cases mne2: m = 2 * Real.exp 2
    have: 1 < Real.exp 2 := by
      have: 0 < (2:ℝ) := by norm_num
      exact Real.one_lt_exp_iff.mpr this
    linarith
    push_neg at mne2
    have logne: -2 ≠ Real.log (2/m) := by
      by_contra! hc
      have: (-2:ℝ) = Real.log (2/(2*Real.exp 2)) := by
        have: 2/(2*Real.exp 2) = 1/(Real.exp 2) := by ring
        rw [this]
        have: 1/(Real.exp 2) = Real.exp (-2) := by
          simp
          exact Eq.symm (Real.exp_neg 2)
        rw [this]
        exact Eq.symm (Real.log_exp (-2))
      rw [this] at hc
      have h2: (2 / (2 * Real.exp 2)) = 2/m := by
        have ht1:  2 / (2 * Real.exp 2) ∈ Set.Ioi 0 := by
          simp
          exact Real.exp_pos 2
        have ht2: 2 / m ∈ Set.Ioi 0 := by
          exact m2pos
        apply Real.log_injOn_pos ht1 ht2 hc
      have: m = 2 * Real.exp 2 := by
        have ht1: 2 / (2 * Real.exp 2) * m = 2 / m * m := by
          exact (mul_left_inj' (id (Ne.symm mnez))).mpr h2
        have ht2: 2 / m * m = 2 := by
          exact div_mul_cancel₀ 2 (id (Ne.symm mnez))
        rw [ht2] at ht1
        have ht3: 1/2 * (2 / (2 * Real.exp 2) * m) = 1/2 * 2 := by
          exact congrArg (HMul.hMul (1 / 2)) ht1
        have: 1 / 2 * (2 / (2 * Real.exp 2) * m) = (2 * Real.exp 2)⁻¹ * m := by ring
        rw [this] at ht3
        have: (1/2:ℝ) * 2 = 1 := by simp
        rw [this] at ht3
        have ht4: (2*Real.exp 2) * ((2*Real.exp 2)⁻¹ * m) = (2*Real.exp 2) * 1 := by
          exact congrArg (HMul.hMul (2 * Real.exp 2)) ht3
        have: 2 * Real.exp 2 * ((2 * Real.exp 2)⁻¹ * m) = m := by
          rw [← mul_assoc]
          have: 2 * Real.exp 2 * (2 * Real.exp 2)⁻¹ = 1 := by
            have nez: 0 ≠ 2 * Real.exp 2 := by
              have htt1: 0 ≠ (2:ℝ) := by norm_num
              have htt2: 0 ≠ Real.exp 2 := by
                exact Ne.symm (Real.exp_ne_zero 2)
              exact Ne.symm (mul_ne_zero (id (Ne.symm htt1)) (id (Ne.symm htt2)))
            exact CommGroupWithZero.mul_inv_cancel (2 * Real.exp 2) (id (Ne.symm nez))
          rw [this]
          simp
        rw [this] at ht4
        simp at ht4
        exact ht4
      contradiction
    have logpos: 0 < Real.log (2 / m) + 2 := by
      have: 0 ≠ Real.log (2/m) + 2 := by
        have: -2 + 2 ≠ Real.log (2/m) + 2 := by
          exact (add_ne_add_left 2).mpr logne
        simp at this
        simp [this]
      apply lt_of_le_of_ne h1 this
    have h2: Real.log (2 / m) ≤ 0 := by
      apply nonpos_of_mul_nonpos_left ineq3 logpos
    have h3: 2/m ≤ 1 := by
      apply (Real.log_nonpos_iff m2pos).mp h2
    have h4: 2/m * m ≤ 1 * m := by
      exact (mul_le_mul_iff_of_pos_right mpos).mpr h3
    simp at this
    have: 2/m * m = 2 := by
      exact div_mul_cancel₀ 2 (id (Ne.symm mnez))
    rw [this] at h4
    linarith [h4]
  simp
  exact ⟨m_lower, m_upper⟩
  -- mpr direction
  intro hm x hx
  have: m * (Real.exp x * (x - (1 - 2))) - x * (x + 4) = g x := by
    rw [g_def, f1_def]
  rw [this]
  -- this direction is to prove g(x) ≥ 2.
  -- we will calculate derivative of g(x), and find its minimum
  -- to use first order derivative to find minimum, we must show the function is continuous and differentiable.
  -- the aim is to show g(x) is decreasing on [-2, x0] and increasing on [x0, ∞)
  -- thus g(x0) is minimum.
  have gconv: Convex ℝ (Set.Ici (-2:ℝ)) := by
    exact convex_Ici (-2)
  have gcont: ContinuousOn g (Set.Ici (-2)) := by
    have: ∀ x ∈ Set.Ici (-2:ℝ), ContinuousAt g x := by
      intro y hy
      simp at hy
      rw [g_def']
      have con1: ContinuousAt (fun y => m * f1 y) y := by
        have ht1: ContinuousAt f1 y := by
          have htt1: ContinuousAt Real.exp y := by
            have: Continuous Real.exp := Real.continuous_exp
            exact Continuous.continuousAt this
          have htt2: ContinuousAt (fun x => x + 1) y := by
            have h11: ContinuousAt (fun x => (1:ℝ)) y := by
              exact continuousAt_const
            have h22: ContinuousAt (fun x => x) y := fun ⦃U⦄ a => a
            apply ContinuousAt.add h22 h11
          rw [f1_def']
          exact ContinuousAt.mul htt1 htt2
        have ht2: ContinuousAt (fun y => m) y := by
          exact continuousAt_const
        exact ContinuousAt.mul ht2 ht1
      have con2: ContinuousAt f2 y := by
        rw [f2_def']
        have idcon: ContinuousAt (fun x => x) y := by
          exact fun ⦃U⦄ a => a
        have ht1: ContinuousAt (fun y => -y^2) y := by
          have: ContinuousAt (fun y => y^2) y := by
            apply ContinuousAt.pow idcon 2
          exact ContinuousAt.neg this
        have ht2: ContinuousAt (fun (y:ℝ) => 4 * y) y := by
          have: ContinuousAt (fun y => (4:ℝ)) y := by
            exact continuousAt_const
          apply ContinuousAt.mul this idcon
        exact ContinuousAt.sub ht1 ht2
      apply ContinuousAt.add con1 con2
    exact ContinuousAt.continuousOn this
  have gdiff: DifferentiableOn ℝ g (interior (Set.Ici (-2:ℝ))) := by
    rw [g_def']
    have difid: DifferentiableOn ℝ (fun (y:ℝ) => y) (interior (Set.Ici (-2))) := by
      exact differentiableOn_id'
    have dif1: DifferentiableOn ℝ (fun y => m * f1 y) (interior (Set.Ici (-2))) := by
      have h1: DifferentiableOn ℝ f1 (interior (Set.Ici (-2))) := by
        exact Differentiable.differentiableOn h
      exact DifferentiableOn.const_mul h1 m
    have dif2: DifferentiableOn ℝ f2 (interior (Set.Ici (-2))) := by
      rw [f2_def']
      have htt1: DifferentiableOn ℝ (fun (y:ℝ) => -y ^ 2) (interior (Set.Ici (-2))) := by
        have: DifferentiableOn ℝ (fun (y:ℝ) => y ^ 2) (interior (Set.Ici (-2))) := by
          exact differentiableOn_pow 2
        exact differentiableOn_neg_iff.mpr this
      have htt2: DifferentiableOn ℝ (fun (y:ℝ) => 4*y) (interior (Set.Ici (-2))) := by
        apply DifferentiableOn.const_mul difid
      exact (DifferentiableOn.sub_iff_right htt1).mpr htt2
    exact (DifferentiableOn.add_iff_right dif1).mpr dif2
  let x0 := Real.log (2/m)
  have x0_def: x0 = Real.log (2/m) := rfl
  by_cases mneq: m = 2* Real.exp 2
  -- when m = 2e^2, x0 = -2, function is increasing on [-2,∞).
  -- thus the minimum is at g(-2). so we single out this case.
  have monotoneon_g: MonotoneOn g (Set.Ici (-2:ℝ)) := by
    have hderiv: ∀ x ∈ interior (Set.Ici (-2)), 0 ≤ deriv g x := by
      intro y hy
      rw [g_deriv, mneq]
      simp
      have h1: 0 ≤ (y+2) := by
        simp at hy
        linarith [hy]
      have h2: 0 ≤ (2 * Real.exp 2 * Real.exp y - 2) := by
        have: 2 * Real.exp 2 * Real.exp y - 2 = 2*(Real.exp 2 * Real.exp y - 1) := by ring
        rw [this]
        have ht1: 0 < (2:ℝ) := by norm_num
        have ht2: 0 ≤ (Real.exp 2 * Real.exp y - 1) := by
          have: Real.exp 2 * Real.exp y = Real.exp (y+2) := by
            rw [mul_comm]
            exact Eq.symm (Real.exp_add y 2)
          rw [this]
          have h2: Real.exp (y + 2) ≥ 1 := by
            exact Real.one_le_exp h1
          exact sub_nonneg_of_le h2
        exact (mul_nonneg_iff_of_pos_left ht1).mpr ht2
      exact Left.mul_nonneg h1 h2
    exact monotoneOn_of_deriv_nonneg gconv gcont gdiff hderiv
  have eqg2: g (-2:ℝ) = 2 := by
    rw [g_def, f1_def', mneq]
    simp
    ring
    have: Real.exp 2 * Real.exp (-2) = 1 := by
      have: Real.exp 2 * Real.exp (-2) = Real.exp (2 + -2) := by
        exact Eq.symm (Real.exp_add 2 (-2))
      simp at this
      rw [this]
    simp [this]
    norm_num
  have: g x ≥ g (-2:ℝ) := by
    have ht1: (-2:ℝ) ∈ Set.Ici (-2) := by simp
    apply monotoneon_g ht1 hx hx
  rwa [eqg2] at this
  -- now, m ≠ 2*e^2
  -- we show that g(x0) is minimum by proving g(x) first decrease then increase.
  push_neg at mneq
  simp at hm
  rcases hm with ⟨m_lower, m_upper⟩
  have m_upper: m < 2*Real.exp 2 := by
    exact lt_of_le_of_ne m_upper mneq
  have hx0: (-2:ℝ) < x0 := by
    rw [x0_def]
    have: (-2:ℝ) = Real.log (Real.exp (-2)) := by
      exact Eq.symm (Real.log_exp (-2))
    rw [this]
    have h1: 0 < Real.exp (-2) := Real.exp_pos (-2)
    have h2: Real.exp (-2) < 2/m := by
      have ht1: Real.exp (-2) * m < Real.exp (-2) * (2 * Real.exp 2)  := by
        exact (mul_lt_mul_iff_of_pos_left h1).mpr m_upper
      have ht2: Real.exp (-2) * (2 * Real.exp 2) = 2 := by
        have: Real.exp (-2) * Real.exp 2 = 1 := by
          have: Real.exp (-2) * Real.exp 2 = Real.exp (-2 + 2) := by
            exact Eq.symm (Real.exp_add (-2) 2)
          rw [this]
          simp
        ring
        simp [this]
      rw [ht2] at ht1
      have ht3: 2 = 2/m * m := by
        have: m ≠ 0 := by
          linarith [m_lower]
        exact Eq.symm (div_mul_cancel₀ 2 this)
      nth_rewrite 2 [ht3] at ht1
      have mpos: 0 < m := by linarith [m_lower]
      exact (mul_lt_mul_iff_of_pos_right mpos).mp ht1
    exact Real.log_lt_log h1 h2
  have anti_g1 : AntitoneOn g (Set.Icc (-2:ℝ) x0) := by
    have hsubst: (Set.Icc (-2:ℝ) x0) ⊆ (Set.Ici (-2)) := by
      exact Set.Icc_subset_Ici_self
    have hsubst': interior (Set.Icc (-2) x0) ⊆ interior (Set.Ici (-2)) := by
      exact interior_mono hsubst
    have conv1: Convex ℝ (Set.Icc (-2:ℝ) x0) := by
      exact convex_Icc (-2) x0
    have cont1: ContinuousOn g (Set.Icc (-2:ℝ) x0) := by
      apply ContinuousOn.mono gcont hsubst
    have diff1: DifferentiableOn ℝ g (interior (Set.Icc (-2:ℝ) x0)) := by
      apply DifferentiableOn.mono gdiff hsubst'
    have deriv1: ∀ x ∈ interior (Set.Icc (-2:ℝ) x0), deriv g x ≤ 0 := by
      intro y hy
      rw [g_deriv]
      simp
      simp at hy
      rcases hy with ⟨ylow,yup⟩
      have h1: 0 < y+2 := by linarith [ylow]
      have h2: (m * Real.exp y - 2) < 0 := by
        have h11: 0 < m := by linarith [m_lower]
        have h22: 0 < (2:ℝ) := by norm_num
        have h33: m ≠ (0:ℝ) := by linarith [h11]
        have ht1: Real.exp y < Real.exp x0 := by
          exact Real.exp_lt_exp.mpr yup
        rw [x0_def] at ht1
        have: Real.exp (Real.log (2 / m)) = 2/m := by
          have: 0 < 2/m := div_pos h22 h11
          apply Real.exp_log this
        rw [this] at ht1
        have ht2: Real.exp y * m < 2/m * m := by
          exact (mul_lt_mul_iff_of_pos_right h11).mpr ht1
        rw [mul_comm]
        have: 2 / m * m = 2 := by
          apply div_mul_cancel₀
          exact h33
        rw [this] at ht2
        linarith [ht2]
      have h3: (m * Real.exp y - 2) ≤ 0 := le_of_lt h2
      exact Linarith.mul_nonpos h3 h1
    exact antitoneOn_of_deriv_nonpos conv1 cont1 diff1 deriv1
  have mono_g1: MonotoneOn g (Set.Ici x0) := by
    have hsubst: (Set.Ici x0) ⊆ (Set.Ici (-2)) := by
      intro x hx
      simp at hx
      have: -2 < x := gt_of_ge_of_gt hx hx0
      exact Set.mem_Ici_of_Ioi this
    have hsubst': interior (Set.Ici x0) ⊆ interior (Set.Ici (-2)) := by
      exact interior_mono hsubst
    have conv2: Convex ℝ (Set.Ici x0) := by
      exact convex_Ici x0
    have cont2: ContinuousOn g (Set.Ici x0) := by
      apply ContinuousOn.mono gcont hsubst
    have diff2: DifferentiableOn ℝ g (interior (Set.Ici x0)) := by
      apply DifferentiableOn.mono gdiff hsubst'
    have deriv2: ∀ x ∈ interior (Set.Ici x0), 0 ≤ deriv g x := by
      intro y hy
      simp at hy
      rw [g_deriv]
      simp
      have h1: 0 ≤ (y + 2) := by
        have: -2 < y := gt_trans hy hx0
        linarith [this]
      have h2: 0 ≤ (m * Real.exp y - 2) := by
        have pos2: 0 < (2:ℝ) := by norm_num
        have mpos: 0 < m := by linarith [m_lower]
        have mnez: m ≠ 0 := by linarith [mpos]
        have ht1: 2/m <  Real.exp y := by
          have: 2/m = Real.exp x0 := by
            rw [x0_def]
            have: 0 < 2 / m := by
              exact div_pos pos2 mpos
            symm
            apply Real.exp_log this
          rw [this]
          exact Real.exp_lt_exp.mpr hy
        have ht2: (2:ℝ) < m * Real.exp y := by
          rw [mul_comm]
          have: (2:ℝ) = (2/m) * m := by
            symm
            apply div_mul_cancel₀ (2:ℝ) mnez
          rw [this]
          exact (mul_lt_mul_iff_of_pos_right mpos).mpr ht1
        linarith [ht2]
      exact Left.mul_nonneg h1 h2
    exact monotoneOn_of_deriv_nonneg conv2 cont2 diff2 deriv2
  have gmin1: ∀y:ℝ, (-2 ≤ y ∧ y ≤ x0) → g y ≥ g x0 := by
    intro y hy
    have h1: y ∈ (Set.Icc (-2) x0) := hy
    have h2: x0 ∈ Set.Icc (-2) x0 := by
      have: (-2:ℝ) ≤ x0 := le_of_lt hx0
      simp [this]
    apply anti_g1 h1 h2 hy.right
  have gmin2: ∀y:ℝ, y ≥ x0 → g y ≥ g x0 := by
    intro y hy
    have h1: y ∈ (Set.Ici x0) := by simp [hy]
    have h2: x0 ∈ (Set.Ici x0) := by simp
    apply mono_g1 h2 h1 hy
  -- argue g(x) ≥ g(x0)
  have gmin: g x ≥ g x0 := by
    have h1: (-2:ℝ) ≤ x := hx
    by_cases xwithx0: x ≤ x0
    apply gmin1 x ⟨h1, xwithx0⟩
    push_neg at xwithx0
    have xge: x ≥ x0 := by linarith [xwithx0]
    apply gmin2 x xge
  -- argue g(x0) ≥ 2. g(x0) depends on m, and 2 ≤ m ≤ 2e^2.
  -- some calculation.
  have gx0eq: g x0 ≥ (2:ℝ) := by
    rw [g_def, f1_def']
    simp
    have mpos: 0 < m := by linarith [m_lower]
    have mnez: m ≠ 0 := by linarith [mpos]
    have p2os: 0 < (2:ℝ) := by norm_num
    have m2pos: 0 < 2/m := div_pos p2os mpos
    have: Real.exp x0 = 2/m := by
      have pos2: 0 < (2:ℝ) := by norm_num
      have mpos: 0 < m := by linarith [m_lower]
      rw [x0_def]
      have: 0 < 2 / m := div_pos pos2 mpos
      apply Real.exp_log this
    rw [this]
    rw [x0_def]
    have: m * (2 / m * (Real.log (2 / m) + 1)) = 2 * Real.log (2/m) + 2 := by
      field_simp
      ring
    rw [this]
    repeat rw [← x0_def]
    have: 2 * x0 + 2 - x0 * (x0 + 4) = - (x0+1)^2 + 3 := by ring
    rw [this]
    -- now, we should prove 2 ≤ -(x0+1)^2+3
    -- equivalently, (x0+1)^2 ≤ 1
    have ineq: (x0+1)^2 ≤ 1 := by
      let x1 := x0+1
      have x1_def: x1 = x0+1 := rfl
      have x1_lower: (-1:ℝ) < x1 := by
        rw [x1_def]
        have: (-2:ℝ) = -1 + -1 := by norm_num
        rw [this] at hx0
        linarith [hx0]
      have x1_upper: x1 ≤ 1 := by
        have h1: Real.log (2/m) ≤ (0:ℝ) := by
          have: (0:ℝ) = Real.log 1 := Eq.symm Real.log_one
          rw [this]
          have h2: 2/m ≤ 1 := by
            exact (div_le_one₀ mpos).mpr m_lower
          exact Real.log_le_log m2pos h2
        rw [x1_def]
        rw [← x0_def] at h1
        linarith [h1]
      rw [← x1_def]
      have: |x1| ≤ 1 := by
        have h1: -1 ≤ x1 := le_of_lt x1_lower
        have h2: -1 ≤ x1 ∧ x1 ≤ 1 := ⟨h1, x1_upper⟩
        apply abs_le.mpr h2
      exact (sq_le_one_iff_abs_le_one x1).mpr this
    linarith [ineq]
  exact Preorder.le_trans 2 (g x0) (g x) gx0eq gmin
exact ⟨tangent_line, range_m⟩
