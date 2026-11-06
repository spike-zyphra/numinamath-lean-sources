import Mathlib

open Real

/- 7. Given $\operatorname{tg} 2 \alpha=\frac{3}{4}, \alpha \in\left(-\frac{\pi}{2}, \frac{\pi}{2}\right)$, when the function $f(x)=\sin (x+2)+$ $\sin (\alpha-x)-2 \sin \alpha$ has a minimum value of 0, find the values of $\cos 2 \alpha$ and $\operatorname{tg} \frac{\alpha}{2}$. -/
theorem algebra_196501 (α : ℝ) (hα : α ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) (htg : Real.tan (2 * α) = 3 / 4)
    (f : ℝ → ℝ) (hf : f = fun x => Real.sin (x + α) + Real.sin (α - x) - 2 * Real.sin α)
    (hmin : ∀ x, 0 ≤ f x) :
    Real.cos (2 * α) = -4 / 5 ∧ Real.tan (α / 2) = (1 - Real.sqrt 10) / 3 := by
  -- Show that f(x) = 2 * sin α * (cos x - 1).
  have eq x : f x = 2 * sin α * (cos x - 1) := by
    simp [mul_sub, two_mul_sin_mul_cos, hf, add_comm]
  -- Show that 0 ≤ f(x) = 2 * sin α * (cos x - 1) implies sin α ≤ 0.
  have hsin : sin α ≤ 0 := by
    contrapose! hmin
    -- Suppose that 0 < sin α and show that 2 * sin α * (cos x - 1) > 0 for x = π / 3.
    use π / 3
    simp [eq]
    linarith
  -- 0 < cos α because α in (-π / 2, π / 2).
  have hcos : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    rw [show -(π / 2) = -π / 2 by ring]
    exact hα
  -- Prove that tan α = -3.
  have htan : tan α = -3 := by
    -- tan (2α) = 2 * tan α / (1 - tan α ^ 2) = 3 / 4.
    rw [tan_two_mul] at htg
    have : 1 - tan α ^ 2 ≠ 0 := by
      contrapose! htg
      rw [htg]
      norm_num
    field_simp [this] at htg
    -- We get 3 * (tan α + 3) * (tan α - 1 / 3) = 0.
    replace htg : 3 * (tan α + 3) * (tan α - 1 / 3) = 0 := by
      linear_combination htg
    simp_rw [mul_eq_zero, show ¬ 3 = (0 : ℝ) by norm_num, false_or] at htg
    -- tan α = -3 or tan α = 1 / 3.
    cases' htg with h h
    · linarith
    -- If tan α  = 1 / 3 then show that 0 < sin α (a contradiction with 0 ≤ sin α).
    contrapose! hsin
    -- Indeed, tan α = sin α / cos α = 1 / 3 and 0 < cos α so 0 < sin α.
    replace h : sin α / cos α = 1 / 3 := by
      rwa [tan_eq_sin_div_cos, sub_eq_zero] at h
    field_simp at h
    linarith
  -- We get cos α ^ 2 = 1 / 10 from
  -- tan α = -3 (i.e., sin α = -3 * cos α) and sin α ^ 2 + cos α ^ 2 = 1.
  have hcos2 : cos α ^ 2 = 1 / 10 := by
    field_simp [tan_eq_sin_div_cos] at htan
    linear_combination (3 / 10 * cos α - 1 / 10 * sin α) * htan + cos_sq_add_sin_sq α / 10
  -- We get cos(2α) = 2 * cos α ^ 2 - 1 = 2 * 1 / 10 - 1 = -4 / 5.
  rw [cos_two_mul, hcos2]
  norm_num
  -- It is left to find tan(α / 2) = sin(α / 2) / cos(α / 2).
  rw [tan_eq_sin_div_cos]
  -- We have -π / 2 < α ≤ 0 (because sin α ≤ 0).
  have ⟨ha1, ha2⟩ : -π / 2 < α ∧ α ≤ 0 := by
    simp only [Set.mem_Ioo] at hα
    refine ⟨hα.1, ?_⟩
    contrapose! hsin
    apply sin_pos_of_pos_of_lt_pi hsin (by linarith)
  -- Use formulas for sin (x / 2) and cos (x / 2) to get
  -- tan(α / 2) = -√((1 - cos α) / 2) / √((1 + cos α) / 2).
  rw [sin_half_eq_neg_sqrt (by linarith) ha2]
  rw [cos_half (by linarith) (by linarith)]
  -- From a ≤ 0 and cos α ^ 2 = 1 / 10, we get cos α = 1 / √10.
  replace hcos : cos α = 1 / √10 := by
    apply_fun sqrt at hcos2
    rw [sqrt_sq (by linarith)] at hcos2
    rw [hcos2, sqrt_div zero_le_one, sqrt_one]
  rw [hcos]
  -- It is left to show that
  -- -√((1 - 1 / √10) / 2) / √((1 + 1 / √10) / 2) = (1 - √10) / 3.
  calc
    _ = -(√((1 - 1 / √10) / 2) * √((1 + 1 / √10) / 2) / (√((1 + 1 / √10) / 2) * √((1 + 1 / √10) / 2))) := by
      rw [mul_div_mul_right _ _ (by positivity), neg_div]
    _ = -(√((1 - 1 / 10) / 4) / ((1 + 1 / √10) / 2)) := by
      rw [← pow_two, sq_sqrt (by positivity)]
      congr
      rw [← sqrt_mul]
      · congr 1
        ring_nf
        rw [show (√10)⁻¹ ^ 2 = 1 / (√10 ^ 2) by ring]
        rw [sq_sqrt (by norm_num)]
        norm_num
      · apply div_nonneg _ zero_le_two
        rw [sub_nonneg]
        rw [← sq_le_sq₀ (by positivity) zero_le_one]
        rw [div_pow, sq_sqrt (by norm_num)]
        norm_num
    _ = (1 - √10) / 3 := by
      field_simp
      ring_nf
      rw [show √10 ^ 3 = √10 ^ 2 * √10 by ring, show √9 = √(3^2) by norm_num, show √4 = √(2^2) by norm_num]
      rw [sq_sqrt (by norm_num), sqrt_sq (by norm_num), sqrt_sq (by norm_num)]
      ring