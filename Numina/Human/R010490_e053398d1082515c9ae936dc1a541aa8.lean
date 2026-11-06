import Mathlib

/- 3. (BUL 3) Prove the trigonometric inequality $\cos x<1-\frac{x^{2}}{2}+\frac{x^{4}}{16}$, where $x \in(0, \pi / 2)$. -/
theorem inequalities_24662 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi/2))

: Real.cos x < 1 - x^2/2 + x^4/16 := by

  -- Consider the function f defined by f(x)=1-x^2/2+x^4/16-cos x.
  let f := fun t : ℝ => 1 - t^2/2 + t^4/16 - Real.cos t

  -- Formula for f'
  have hf' : deriv f = (fun t => -t + t^3/4 + Real.sin t) := by
    unfold f
    ext t
    rw [deriv_sub, deriv_add, deriv_sub, deriv_const, deriv_div_const, deriv_pow]
    field_simp
    ring
    all_goals fun_prop

  -- Formula for f''
  have hf'' : deriv (deriv f) = (fun t => -1 + 3*t^2/4 + Real.cos t) := by
    rw [hf']
    ext t
    rw [deriv_add, deriv_add]
    simp
    all_goals fun_prop

  -- Formula for f'''
  have hf''' : deriv (deriv (deriv f)) = (fun t => 3*t/2 - Real.sin t) := by
    rw [hf'']
    ext t
    rw [deriv_add, deriv_add, deriv_const, deriv_div_const]
    field_simp
    ring
    all_goals fun_prop

  -- Formula for f''''
  have hf'''' : deriv (deriv (deriv (deriv f))) = (fun t => 3/2 - Real.cos t) := by
    rw [hf''']
    ext t
    rw [deriv_sub]
    field_simp
    rw [deriv_const_mul, deriv_id'', mul_one]
    all_goals fun_prop

  -- f(0) = 0
  have h_f_0 : f 0 = 0 := by
    unfold f
    norm_num

  -- f'(0) = 0
  have h_f'_0 : (deriv f) 0 = 0 := by
    rw [hf']
    simp

  -- f''(0) = 0
  have h_f2_0 : (deriv (deriv f)) 0 = 0 := by
    rw [hf'']
    simp

  -- f'''(0) = 0
  have h_f3_0 : (deriv (deriv (deriv f))) 0 = 0 := by
    rw [hf''']
    simp

  -- Define D := [0, pi/2), which is the domain of f over which we will prove properties
  let D := Set.Ico 0 (Real.pi / 2)

  -- D is a convex set
  have hD_convex : Convex ℝ D := by
    apply convex_Ico

  -- Interior of D is the open interval (0, pi/2)
  have hD_interior : interior D = Set.Ioo 0 (Real.pi / 2) := by
    rw [interior_Ico]

  -- Continuitity lemmas: f''', f'', f' are continuous on D

  have h_f3_cont : ContinuousOn (deriv (deriv (deriv f))) D := by
    apply Continuous.continuousOn
    rw [hf''']
    fun_prop

  have h_f2_cont : ContinuousOn (deriv (deriv f)) D := by
    apply Continuous.continuousOn
    rw [hf'']
    fun_prop

  have h_f1_cont : ContinuousOn (deriv f) D := by
    apply Continuous.continuousOn
    rw [hf']
    fun_prop

  have h_f_cont : ContinuousOn f D := by
    apply Continuous.continuousOn
    fun_prop

  -- 0 ∈ D
  have ha : 0 ∈ D := by
    rw [Set.left_mem_Ico]
    positivity

  -- 0 < f'''' on the interior of D
  have h_f4_pos: ∀ t ∈ interior D, 0 < deriv (deriv (deriv (deriv f))) t := by
    intro t ht
    rw [hf'''', sub_pos]
    linarith [Real.cos_le_one t]

  -- f''' is strictly monotone on D
  have h_f3_mono := strictMonoOn_of_deriv_pos hD_convex h_f3_cont h_f4_pos

  -- f''' is positive on the interior of D
  have h_f3_pos : ∀ t ∈ interior D, 0 < (deriv (deriv (deriv f))) t := by
    intro t ht
    have ht' : t ∈ D := interior_subset ht

    rw [hD_interior] at ht
    have t_pos : 0 < t := by
      rw [Set.mem_Ioo] at ht
      exact ht.1
    specialize h_f3_mono ha ht' t_pos
    rw [h_f3_0] at h_f3_mono
    exact h_f3_mono

    -- f'' is strictly monotone on D
  have h_f2_mono := strictMonoOn_of_deriv_pos hD_convex h_f2_cont h_f3_pos

  -- f'' is positive on the interior of D
  have h_f2_pos : ∀ t ∈ interior D, 0 < (deriv (deriv f)) t := by
    intro t ht
    have ht' : t ∈ D := interior_subset ht
    rw [hD_interior] at ht
    have t_pos : 0 < t := by
      rw [Set.mem_Ioo] at ht
      exact ht.1
    specialize h_f2_mono ha ht' t_pos
    rw [h_f2_0] at h_f2_mono
    exact h_f2_mono

  -- f' is strictly monotone on D
  have h_f1_mono := strictMonoOn_of_deriv_pos hD_convex h_f1_cont h_f2_pos

  -- f' is positive on the interior of D
  have h_f1_pos : ∀ t ∈ interior D, 0 < (deriv f) t := by
    intro t ht
    have ht' : t ∈ D := interior_subset ht
    rw [hD_interior] at ht
    have t_pos : 0 < t := by
      rw [Set.mem_Ioo] at ht
      exact ht.1
    specialize h_f1_mono ha ht' t_pos
    rw [h_f'_0] at h_f1_mono
    exact h_f1_mono

  -- f is strictly monotone on D
  have h_f_mono := strictMonoOn_of_deriv_pos hD_convex h_f_cont h_f1_pos

  -- f is positive on the interior of D
  have h_f_pos : ∀ t ∈ interior D, 0 < f t := by
    intro t ht
    have ht' : t ∈ D := interior_subset ht
    rw [hD_interior] at ht
    have t_pos : 0 < t := by
      rw [Set.mem_Ioo] at ht
      exact ht.1
    specialize h_f_mono ha ht' t_pos
    rw [h_f_0] at h_f_mono
    exact h_f_mono

  have hx' : x ∈ interior D := by
    rw [hD_interior]
    exact hx

  specialize h_f_pos x hx'
  unfold f at h_f_pos
  linarith
