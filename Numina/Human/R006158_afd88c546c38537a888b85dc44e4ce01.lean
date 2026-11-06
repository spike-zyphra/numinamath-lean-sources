import Mathlib
open Real


-- In Lean, tan(pi/2) is defined as 0, which is different from the usual definition in mathematics. It is necessary to add the condition cos x ≠ 0.
theorem algebra_624931
  (S : Set ℝ)
  (hS : S = {x : ℝ | x ∈ Set.Ioo 0 (2 * π) ∧ cos x ≠ 0 ∧ 3 * tan x ^ 2 + 8 * tan x + 3 = 0}) :
    ∑ᶠ x ∈ S, x = 5 * π := by

  have : π > 0 := by positivity
  have : √7 > 0 := by positivity

  let t1 := (-4 - √7)/3
  let t2 := (-4 + √7)/3
  let x1 := arctan t1
  let x2 := arctan t2


  have h_t1_lt_zero : t1 < 0 := by
    unfold t1
    linarith

  have h_t2_lt_zero : t2 < 0 := by
    unfold t2
    suffices √7 < 4 by linarith
    rw [sqrt_lt (by norm_num) (by norm_num)]
    norm_num

  have h_x1_range1 : -(π/2) < x1 := by
    unfold x1
    exact neg_pi_div_two_lt_arctan t1

  have h_x1_range2 : x1 < 0 := by
    unfold x1
    rw [show 0 = arctan 0 by simp]
    apply arctan_strictMono
    exact h_t1_lt_zero

  have h_x2_range1 : -(π/2) < x2 := by
    unfold x2
    exact neg_pi_div_two_lt_arctan t2

  have h_x2_range2 : x2 < 0 := by
    unfold x2
    rw [show 0 = arctan 0 by simp]
    apply arctan_strictMono
    exact h_t2_lt_zero

  have h_x1_ne_x2 : x1 ≠ x2 := by
    by_contra h
    unfold x1 x2 at h
    apply arctan_injective at h
    unfold t1 t2 at h
    linarith

  have h_cos_x1_neq_zero : cos x1 ≠ 0 := by
    have := cos_arctan_pos t1
    unfold x1
    linarith

  have h_cos_x2_neq_zero : cos x2 ≠ 0 := by
    have := cos_arctan_pos t2
    unfold x2
    linarith

  have h_t2_eq_inv_t1 : t2 = t1⁻¹:= by
    have : t1 ≠ 0 := by linarith
    field_simp
    unfold t1 t2
    ring_nf
    rw [sq_sqrt (by positivity)]
    field_simp
    ring_nf

  have h_x1_add_x2 : x1 + x2 = -π/2 := by
    unfold x1 x2
    rw [h_t2_eq_inv_t1, arctan_inv_of_neg h_t1_lt_zero]
    ring

  suffices S = {x1 + π, x2 + π, x1 + 2*π, x2 + 2*π} by
    rw [this]
    rw [finsum_mem_eq_toFinset_sum]
    simp
    repeat rw [Finset.sum_insert]
    simp
    rw [show x1 = -π/2 - x2 by linarith]
    ring_nf
    . simp
      exact h_x1_ne_x2
    . simp
      constructor
      . by_contra
        linarith
      . by_contra
        linarith
    . simp
      refine ⟨h_x1_ne_x2, ?_, ?_⟩
      . by_contra
        linarith
      . by_contra
        linarith

  rw [hS]
  ext x
  simp
  constructor
  . intro ⟨ ⟨ hx1, hx2⟩, hx3, hx4 ⟩
    have h1 : tan x = t1 ∨ tan x = t2 := by
      have : 3 * (tan x - t1) * (tan x - t2) = 0 := by
        rw [← hx4]
        unfold t1 t2
        ring_nf
        rw [sq_sqrt (by positivity)]
        field_simp
        ring_nf
      simp at this
      rcases this with h1 | h1
      . left; linarith
      . right; linarith

    rcases h1 with h1 | h1
    . have h2 : sin (x-x1) = 0 := by
        rw [sin_sub]
        rw [tan_eq_sin_div_cos] at h1
        field_simp at h1
        rw [h1]
        have : t1 = tan x1 := by
          unfold x1
          simp
        rw [this]
        rw [tan_eq_sin_div_cos]
        field_simp
        ring_nf
      rw [sin_eq_zero_iff] at h2
      obtain ⟨ n, hn ⟩ := h2

      have h3: x - x1 < 3 * π := by
        linarith

      have h4: 0 < x - x1 := by
        linarith

      have h5: 0 < n := by
        rw [← hn] at h4
        field_simp at h4
        norm_cast at h4

      have h6: n < 3 := by
        rw [← hn] at h3
        field_simp at h3
        norm_cast at h3

      interval_cases n
      . left; simp at hn; linarith
      . right; right; left; simp at hn; linarith

    . have h2 : sin (x-x2) = 0 := by
        rw [sin_sub]
        rw [tan_eq_sin_div_cos] at h1
        field_simp at h1
        rw [h1]
        have : t2 = tan x2 := by
          unfold x2
          simp

        rw [this]
        rw [tan_eq_sin_div_cos]

        field_simp
        ring_nf

      rw [sin_eq_zero_iff] at h2
      obtain ⟨ n, hn ⟩ := h2

      have h3: x - x2 < 3 * π := by
        linarith

      have h4: 0 < x - x2 := by
        linarith

      have h5: 0 < n := by
        rw [← hn] at h4
        field_simp at h4
        norm_cast at h4

      have h6: n < 3 := by
        rw [← hn] at h3
        field_simp at h3
        norm_cast at h3

      interval_cases n
      . right; left; simp at hn; linarith
      . right; right; right; simp at hn; linarith

  . intro hx
    refine ⟨ ⟨ ?_, ?_ ⟩, ?_, ?_ ⟩
    . rcases hx with rfl | rfl | rfl | rfl
      all_goals linarith
    . rcases hx with rfl | rfl | rfl | rfl
      all_goals linarith
    . rcases hx with rfl | rfl | rfl | rfl
      . rw [cos_add_pi]
        by_contra h
        simp at h
        unfold x1 at h
        rw [cos_arctan] at h
        unfold t1 at h
        ring_nf at h
        rw [sq_sqrt (by positivity)] at h
        field_simp at h
      . rw [cos_add_pi]
        by_contra h
        simp at h
        unfold x2 at h
        rw [cos_arctan] at h
        unfold t2 at h
        ring_nf at h
        rw [sq_sqrt (by positivity)] at h
        field_simp at h
        rw [sqrt_eq_zero'] at h
        ring_nf at h
        have : 4 ≤ √7 := by linarith
        rw [le_sqrt (by norm_num) (by norm_num)] at this
        norm_num at this
      . rw [cos_add_two_pi]
        by_contra h
        unfold x1 at h
        rw [cos_arctan] at h
        unfold t1 at h
        ring_nf at h
        rw [sq_sqrt (by positivity)] at h
        field_simp at h
      . rw [cos_add_two_pi]
        by_contra h
        unfold x2 at h
        rw [cos_arctan] at h
        unfold t2 at h
        ring_nf at h
        rw [sq_sqrt (by positivity)] at h
        field_simp at h
        rw [sqrt_eq_zero'] at h
        ring_nf at h
        have : 4 ≤ √7 := by linarith
        rw [le_sqrt (by norm_num) (by norm_num)] at this
        norm_num at this

    . rcases hx with rfl | rfl | rfl | rfl
      . rw [tan_add_pi]
        unfold x1
        simp
        unfold t1
        ring_nf
        rw [sq_sqrt (by positivity)]
        linarith
      . rw [tan_add_pi]
        unfold x2
        simp
        unfold t2
        ring_nf
        rw [sq_sqrt (by positivity)]
        linarith
      . rw [show x1 + 2 * π = x1 + π + π by ring]
        rw [tan_add_pi]
        rw [tan_add_pi]
        unfold x1
        simp
        unfold t1
        ring_nf
        rw [sq_sqrt (by positivity)]
        linarith
      . rw [show x2 + 2 * π = x2 + π + π by ring]
        rw [tan_add_pi]
        rw [tan_add_pi]
        unfold x2
        simp
        unfold t2
        ring_nf
        rw [sq_sqrt (by positivity)]
        linarith
