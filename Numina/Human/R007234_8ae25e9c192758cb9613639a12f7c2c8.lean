import Mathlib

open Real Set


/- Let $\alpha, \beta$ and $\gamma$ be three angles with $0 \leq \alpha, \beta, \gamma<90^{\circ}$ and $\sin \alpha+\sin \beta+\sin \gamma=1$. Show that

$$
\tan ^{2} \alpha+\tan ^{2} \beta+\tan ^{2} \gamma \geq \frac{3}{8}
$$ -/
theorem inequalities_239161 (α β γ : ℝ)
  (h₀ : α ∈ Ico 0 (π / 2)) (h₁ : β ∈ Ico 0 (π / 2)) (h₂ : γ ∈ Ico 0 (π / 2))
  (h₃ : sin α + sin β + sin γ = 1) :
  tan α ^ 2 + tan β ^ 2 + tan γ ^ 2 ≥ 3 / 8 := by

  -- 0 < cos x if 0 ≤ x < π/2
  have cos_pos_of {x:ℝ} (hx: x ∈ Ico 0 (π/2)):
    0 < cos x := by
    apply cos_pos_of_mem_Ioo ?_
    simp only [mem_Ioo, mem_Ico] at hx ⊢
    constructor <;> linarith only [hx]

  -- (tan x)^2 = 1/(cos x)^2 - 1
  have tan_sq_of_cos {x:ℝ} (hx: x ∈ Ico 0 (π/2)):
    (tan x)^2 = 1 / (cos x)^2 - 1 := by
    have: cos x ≠ 0 := by
      symm; apply ne_of_lt
      apply cos_pos_of hx
    rw [← inv_one_add_tan_sq this]
    simp only [div_inv_eq_mul, one_mul, add_sub_cancel_left]

  -- then it suffices to prove
  -- 1/(cos α)^2 + 1/(cos β)^2 + 1/(cos γ)^2 ≥ 27/8
  suffices 1/(cos α)^2 + 1/(cos β)^2 + 1/(cos γ)^2 ≥ 27/8 by
    simp only [tan_sq_of_cos, h₀, h₁, h₂]
    linarith only [this]


  set s := Finset.range 3 with s_def
  have hs: s.Nonempty := by
    simp [s_def]

  set z: ℕ → ℝ := fun i =>
      match i with
      | 0 => (cos α)^2
      | 1 => (cos β)^2
      | 2 => (cos γ)^2
      | i+3 => 0
      with z_def

  set z': ℕ → ℝ := fun i =>
      match i with
      | 0 => (sin α)
      | 1 => (sin β)
      | 2 => (sin γ)
      | i+3 => 0
      with z'_def

  have hz: ∀ i ∈ s, 0 < z i := by
      intro i hi
      simp only [s_def, Finset.mem_range] at hi
      replace hi: i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi with (rfl | rfl | rfl)
      all_goals
        simp only [z_def]
        apply pow_pos (cos_pos_of ?_) 2
        assumption

  have hz': ∀i ∈ s, 0 ≤ z' i := by
    intro i hi
    simp only [s_def, Finset.mem_range] at hi
    replace hi: i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with (rfl | rfl | rfl)
    all_goals
      simp [mem_Ioo, mem_Ico] at h₀ h₁ h₂ ⊢
      refine sin_nonneg_of_nonneg_of_le_pi ?_ ?_
      <;> linarith only [h₀, h₁, h₂]

  -- recall that harmonic mean ≤ arith mean
  have hm_am: 3/(1/(cos α)^2 + 1/(cos β)^2 + 1/(cos γ)^2) ≤
    ((cos α)^2 + (cos β)^2 + (cos γ)^2) / 3 := by
    set w: ℕ → ℝ := fun _ => 1 with w_def
    have hw: ∀ i ∈ s, 0 < w i := by simp [w_def]
    have hw': 0 < ∑ i ∈ s, w i := by simp [s_def, w_def]
    -- harmonic mean ≤ geom mean ≤ arith mean
    have h1 := harm_mean_le_geom_mean s hs
      w z hw hw' hz
    have h2 := geom_mean_le_arith_mean s w z
      (fun i hi => (le_of_lt (hw i hi))) hw'
      (fun i hi => (le_of_lt (hz i hi)))
    have h3 := le_trans h1 h2
    simp only [s_def, w_def, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one, z_def, one_div,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    one_mul] at h3
    simp only [one_div, h3]

  -- (cos α)^2 = 1 - (sin α)^2,
  -- change right side of the inequality above to sum of sin square.
  have h1: ((cos α)^2 + (cos β)^2 + (cos γ)^2) / 3 =
    1 - ((1/3)*(sin α)^2  + (1/3)*(sin β)^2 + (1/3)*(sin γ)^2) := by
    simp only [cos_sq']
    ring

  -- sin square sum / 3 ≥ (sin sum / 3) square.
  have h2: (1/3)*(sin α)^2  + (1/3)*(sin β)^2 + (1/3)*(sin γ)^2 ≥
    (((1/3)*sin α + (1/3)*sin β + (1/3)*sin γ))^2 := by
    have := pow_arith_mean_le_arith_mean_pow s (fun i => (1/3))
      z' (by simp) (by simp [s_def]) hz' 2
    simp only [s_def, one_div, z'_def, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton] at this
    simp only [one_div, ge_iff_le, this]

  -- by problem statement, sin α + sin β + sin γ = 1, so that sum ≥ 1/9
  have h3: (1/3)*(sin α)^2  + (1/3)*(sin β)^2 +
    (1/3)*(sin γ)^2 ≥ 1/9 := by
    have: ((1/3)*sin α + (1/3)*sin β + (1/3)*sin γ) =
      (sin α + sin β + sin γ) / 3 := by ring
    rw [this, h₃] at h2
    linarith only [h2]

  -- (...) ≥ 1/9, so 1 - (...) ≤ 1 - 1/9 = 8/9
  have h4: ((cos α)^2 + (cos β)^2 + (cos γ)^2) / 3 ≤ 8/9 := by
    rw [h1]
    linarith only [h3]

  -- 3 / X ≤ 8/9, then X ≥ 27/8
  have {X:ℝ} (h: 3 / X ≤ 8/9) (hX: 0 < X): X ≥ 27/8 := by
    have hh1: X * (3/X) ≤ X * (8/9) := by
      apply (mul_le_mul_iff_of_pos_left hX).mpr h
    have hh2: X*(3/X) = 3 := by
      apply mul_div_cancel₀ _ hX.ne'
    rw [hh2] at hh1
    linarith only [hh1]
  -- done.
  apply this (le_trans hm_am h4)
  apply add_pos
  · apply add_pos
    all_goals
      apply div_pos (by norm_num) (pow_pos (cos_pos_of ?_) 2)
      assumption
  · apply div_pos (by norm_num)
    apply pow_pos (cos_pos_of h₂)