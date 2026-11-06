import Mathlib

open Real Set

-- If x ^ 2 + y ^ 2 = 1, then we can trig sub
lemma l_trig_sub {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 + y ^ 2 = 1) :
    ∃ θ ∈ Ioo 0 (π / 2), x = cos θ ∧ y = sin θ := by
  -- Show that x < 1
  have : x < 1 := by
    rw [← sq_lt_sq₀ (by linarith) (by norm_num)]
    nlinarith
  use arccos x
  simp
  exact ⟨⟨by linarith, hx⟩, (cos_arccos (by linarith) (by linarith)).symm, by rw [sin_arccos, ← sq_eq_sq₀ (by positivity) (by positivity), sq_sqrt (by nlinarith)]; linarith⟩

/- 7. Given acute angles $\alpha, \beta$ satisfy the condition: $\frac{\sin ^{4} \alpha}{\cos ^{2} \beta}+\frac{\cos ^{4} \alpha}{\sin ^{2} \beta}=1$, then $\alpha+\beta=$ -/
theorem algebra_199623 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₂ : Real.sin α ^ 4 / Real.cos β ^ 2 + Real.cos α ^ 4 / Real.sin β ^ 2 = 1) :
    α + β = Real.pi / 2 := by
  -- Rewrite so we can apply our trig sub lemma
  rw [show sin α ^ 4 / cos β ^ 2 = (sin α ^ 2 / cos β) ^ 2 by rw [div_pow, ← pow_mul]] at h₂
  rw [show cos α ^ 4 / sin β ^ 2 = (cos α ^ 2 / sin β) ^ 2 by rw [div_pow, ← pow_mul]] at h₂
  -- Show that the trig functions take positive values
  have sin_a_pos : 0 < sin α := by apply sin_pos_of_mem_Ioo; simp at h₀; simp; constructor <;> linarith
  have cos_a_pos : 0 < cos α := by apply cos_pos_of_mem_Ioo; simp at h₀; simp; constructor <;> linarith
  have sin_b_pos : 0 < sin β := by apply sin_pos_of_mem_Ioo; simp at h₁; simp; constructor <;> linarith
  have cos_b_pos : 0 < cos β := by apply cos_pos_of_mem_Ioo; simp at h₁; simp; constructor <;> linarith
  -- Use our trig sub with a new variable θ
  rcases l_trig_sub (by positivity) (by positivity) h₂ with ⟨θ, hθ, hx, hy⟩
  rw [div_eq_iff (by linarith)] at hx
  rw [div_eq_iff (by linarith)] at hy
  -- Add hx and hy
  have h₃ : sin α ^ 2 + cos α ^ 2 = cos θ * cos β + sin θ * sin β := by linear_combination hx + hy
  rw [← cos_sub, sin_sq_add_cos_sq] at h₃
  symm at h₃
  -- Show that θ = β
  rw [cos_eq_one_iff] at h₃
  rcases h₃ with ⟨n, hn⟩
  -- Do case work on whether n is less than or greater than zero and obtain a contradiction in each case
  have n_eq_zero : n = 0 := by
    -- Use contradiction
    by_contra h
    -- Do case work on whether n is less than or greater than zero and obtain a contradiction in each case
    rcases lt_or_gt_of_ne h with lt | gt
    · -- n < 0
      have : n ≤ -1 := by linarith
      rify at this
      have : θ - β ≤ -2 * π := by rw [← hn]; nlinarith [pi_pos]
      simp at hθ h₁
      linarith
    -- n > 0
    have : n ≥ 1 := by linarith
    rify at this
    have : θ - β ≥ 2 * π := by rw [← hn]; nlinarith [pi_pos]
    simp at hθ h₁
    nlinarith
  subst n
  push_cast at hn; rw [zero_mul] at hn; symm at hn; rw [sub_eq_zero] at hn
  subst θ
  -- Show that sin α = cos β and solve
  rw [← pow_two, sq_eq_sq₀ (by positivity) (by positivity), ← sin_pi_div_two_sub, sin_eq_sin_iff] at hx
  rcases hx with ⟨k, hk⟩
  have k_eq_zero : k = 0 := by
    simp at h₁ h₀
    -- Use contradiction
    by_contra h
    -- Casework on hk
    rcases hk with hk | hk
    · -- Do case work on whether k is less than or greater than zero and obtain a contradiction in each case
      rcases lt_or_gt_of_ne h with lt | gt
      · -- k < 0
        have : k ≤ -1 := by linarith
        rify at this
        have : 0 ≤ π / 2 - β := by linarith
        have : _ :=
          calc
            2 * k * π + α ≤ 2 * (-1) * π + π / 2 := by gcongr; linarith;
            _ = -3 * π / 2 := by nlinarith
        linarith
      -- k > 0
      have : k ≥ 1 := by linarith
      rify at this
      nlinarith
    rcases lt_or_gt_of_ne h with lt | gt
    · -- Do casework on whether k is less than or greater than 0
      have : k ≤ -1 := by linarith
      rify at this
      nlinarith
    have : k ≥ 1 := by linarith
    rify at this
    nlinarith
  subst k
  simp at hk
  rcases hk with h | h
  · linarith
  -- This case is impossible
  simp at h₀ h₁
  have : π / 2 - β ≠ π - α := by linarith
  tauto