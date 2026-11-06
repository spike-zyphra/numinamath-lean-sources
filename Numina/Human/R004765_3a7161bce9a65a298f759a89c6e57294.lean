import Mathlib

open Real Set


-- Five. (Full marks 20 points) Let the constant $a>1>b>0$. Then, under what relationship between $a$ and $b$ is the solution set of $\lg \left(a^{x}-b^{x}\right)>0$ $(1, +\infty)$?
theorem algebra_319072 {a b : ℝ}
  (hb : b ∈ Ioo 0 1) (ha : a ∈ Ioi 1) :
  {x | 0 < a ^ x - b ^ x ∧ logb 10 (a ^ x - b ^ x) > 0} = (Ioi (1:ℝ)) ↔ a = b + 1 := by

  let fa := fun x:ℝ => a ^ x
  let fb := fun x:ℝ => b ^ x
  let f1 := fun x => fa x - fb x
  let f2 := fun x => logb 10 (f1 x)

  have h_simp_set : {x | 0 < f1 x ∧ 0 < f2 x} = {x | 1 < f1 x} := by
    ext x
    simp
    constructor
    . intro ⟨ h1, h2 ⟩
      rw [logb_pos_iff (by linarith) (by linarith)] at h2
      linarith
    . intro h1
      unfold f2
      nth_rw 2 [(by norm_num: 0 = logb 10 1)]
      have h2: 0 < f1 x := by linarith
      rw [logb_lt_logb_iff (by norm_num) (by norm_num) h2]
      exact ⟨ h2, h1 ⟩

  have hfa : StrictMono fa := by
    unfold fa StrictMono
    intro x1 x2 hx
    simp
    rw [rpow_lt_rpow_left_iff (by simp at ha; exact ha)]
    exact hx

  have hfb : StrictAnti fb := by
    unfold fb StrictAnti
    intro x1 x2 hx
    simp
    simp at hb
    rw [rpow_lt_rpow_left_iff_of_base_lt_one hb.1 hb.2]
    exact hx

  have hf1 : StrictMono f1:= by
    have := StrictMono.add hfa (StrictAnti.neg hfb)
    exact this

  have hf2 : StrictMonoOn f2 (Ioi 0) := by
    unfold f2 StrictMonoOn
    intro x1 hx1 x2 hx2 hx
    simp
    have := hf1 hx

    have h1 : 0 < f1 x1 := by
      simp at hx1
      have := hf1 hx1
      rw [(by unfold f1 fa fb; norm_num: f1 0 = 0)] at this
      linarith
    have h2 : 0 < f1 x2 := by
      simp at hx2
      have := hf1 hx2
      rw [(by unfold f1 fa fb; norm_num: f1 0 = 0)] at this
      linarith

    rw [logb_lt_logb_iff (by norm_num) h1 h2]
    exact this

  have h_x0 : ∃ x0, f1 x0 = 1 := by
    simp at ha hb

    have f1c: Continuous f1 := by
      -- have fac: Continuous fa := by
      --   apply continuous_const_rpow
      --   simp at ha; linarith
      -- have fbc: Continuous fb := by
      --   apply continuous_const_rpow
      --   simp at hb; linarith
      -- have := Continuous.sub fac fbc
      -- exact this
      have fac: Continuous fa := by
        apply Continuous.rpow
        . exact continuous_const
        . exact continuous_id
        . intro x; left; linarith

      have fbc: Continuous fb := by
        apply Continuous.rpow
        . exact continuous_const
        . exact continuous_id
        . intro x; left; linarith

      have := Continuous.sub fac fbc
      exact this

    have h1:= intermediate_value_univ 0 (logb a 2) f1c

    have h2 : 1 ∈ Icc (f1 0) (f1 (logb a 2)) := by
      simp
      unfold f1 fa fb
      constructor
      . norm_cast
        norm_num
      . rw [rpow_logb (by linarith) (by linarith) (by linarith)]
        suffices b ^ logb a 2 < 1 by linarith
        rw [(by norm_num: 1 = b^(0:ℝ))]
        rw [rpow_lt_rpow_left_iff_of_base_lt_one (by linarith) (by linarith)]
        rw [(by norm_num: 0 = logb a 1)]
        rw [logb_lt_logb_iff ha (by norm_num) (by linarith)]
        norm_num

    exact h1 h2

  constructor
  . intro hx
    unfold f1 f2 fa fb at h_simp_set
    rw [h_simp_set] at hx


    obtain ⟨ x0, hx0 ⟩ := h_x0
    nth_rw 1 [← hx0] at hx

    have : {x | f1 x0 < f1 x} = Ioi 1 := by
      unfold f1
      exact hx

    have : Ioi 1 = Ioi x0 := by
      suffices {x | f1 x0 < f1 x} = Ioi x0 by rw[← this]; symm; assumption
      ext x
      simp
      constructor
      . intro hx
        rcases lt_trichotomy x x0 with (h_lt | rfl | h_gt)
        . have := hf1 h_lt
          linarith
        . simp at hx
        . have := hf1 h_gt
          linarith

      . intro hx
        exact hf1 hx


    have : x0 = 1 := by
      rw [Ioi_inj] at this
      exact this.symm

    unfold f1 fa fb at hx0
    rw [this] at hx0
    norm_cast at hx0
    linarith

  . intro h
    ext x
    simp
    constructor
    . intro ⟨ h1, h2 ⟩
      rw [logb_pos_iff (by linarith) (by linarith)] at h2

      rcases lt_trichotomy x 1 with (h_lt | rfl | h_gt)
      . have := hf1 h_lt
        unfold f1 fa fb at this
        norm_cast at this
        linarith
      . norm_cast at h2
        linarith
      . exact h_gt

    . intro h1

      constructor
      . have : 0 < x := by linarith
        have := hf1 this
        unfold f1 fa fb at this
        norm_cast at this
        linarith

      . have h2 : 1 ∈ Ioi (0:ℝ) := by simp
        have h3 : x ∈ Ioi (0:ℝ) := by simp; linarith

        have := hf2 h2 h3 h1
        unfold f2 f1 fa fb at this
        norm_cast at this

        nth_rw 1 [h] at this

        ring_nf at this
        norm_num at this
        exact this
