import Mathlib

theorem algebra_630980 (a b : ℚ) (ha : |a| > 0) :
  {x | |(abs (x - a)) - b| = 3}.encard = 3 ↔ b = 3 := by


  let S := {x | |(abs (x - a)) - b| = 3}

  have hset1 : b < -3 → S = ∅ := by
    intro hb
    unfold S
    ext x
    simp
    by_contra h
    rw [abs_eq (by norm_num)] at h
    have : |x - a| ≥ 0 := by positivity
    rcases h with h | h
    . linarith
    . linarith

  have hset2 : b ∈ Set.Ico (-3) 3 → S = {a - b - 3, a + b + 3} := by
    intro hb
    simp at hb
    have ⟨ hb1, hb2 ⟩ := hb
    unfold S
    ext x
    simp
    constructor
    . intro hx
      rw [abs_eq (by norm_num)] at hx
      rcases hx with hx | hx
      . have : |x - a| = b + 3 := by linarith
        rw [abs_eq (by linarith)] at this
        rcases this with hx | hx
        . have : x - a = b + 3 := by linarith
          right; linarith
        . have : x - a = -(b + 3) := by linarith
          left; linarith
      . have : |x - a| ≥ 0 := by positivity
        linarith
    . intro hx
      rcases hx with hx | hx
      . subst x
        ring_nf
        nth_rw 2 [abs_of_nonpos (by linarith)]
        ring_nf
        norm_num
      . subst x
        ring_nf
        nth_rw 2 [abs_of_nonneg (by linarith)]
        ring_nf
        norm_num

  have hset3 : 3 ≤ b → S = {a - b - 3, a + b + 3, a + b - 3, a + 3 - b} := by
    intro hb
    unfold S
    ext x
    simp
    constructor
    . intro hx
      rw [abs_eq (by norm_num)] at hx
      rcases hx with hx | hx
      . have : |x - a| = b + 3 := by linarith
        rw [abs_eq (by linarith)] at this
        rcases this with hx | hx
        . have : x - a = b + 3 := by linarith
          right; left; linarith
        . have : x - a = -(b + 3) := by linarith
          left; linarith
      . have : |x - a| = b - 3 := by linarith
        rw [abs_eq (by linarith)] at this
        rcases this with hx | hx
        . have : x - a = b - 3 := by linarith
          right; right; left; linarith
        . have : x - a = -(b - 3) := by linarith
          right; right; right; linarith
    . intro hx
      rcases hx with hx | hx | hx | hx
      . subst x
        ring_nf
        nth_rw 2 [abs_of_nonpos (by linarith)]
        ring_nf
        norm_num
      . subst x
        ring_nf
        nth_rw 2 [abs_of_nonneg (by linarith)]
        ring_nf
        norm_num
      . subst x
        ring_nf
        nth_rw 2 [abs_of_nonneg (by linarith)]
        ring_nf
        norm_num
      . subst x
        ring_nf
        nth_rw 2 [abs_of_nonpos (by linarith)]
        ring_nf
        norm_num

  constructor
  · intro h
    by_cases hb1 : b < -3
    . have := hset1 hb1
      unfold S at this
      rw [this] at h
      simp at h
    . by_cases hb2 : b ∈ Set.Ico (-3) 3
      . have := hset2 hb2
        unfold S at this
        rw [this] at h
        by_cases a - b - 3 = a + b + 3
        . have : b = -3 := by linarith
          subst b
          simp at h
        . rw [Set.encard_insert_of_not_mem (by simp; assumption)] at h
          simp at h
          norm_num at h

      . have hb3 : 3 ≤ b := by
          simp at hb1 hb2
          have := hb2 hb1
          linarith
        have := hset3 hb3
        unfold S at this
        rw [this] at h

        by_contra hb4
        simp at hb4

        have hb5 : 3 < b := lt_of_le_of_ne hb3 (Ne.symm hb4)
        repeat rw [Set.encard_insert_of_not_mem] at h
        . simp at h
          norm_num at h
        . simp
          by_contra h
          linarith
        . simp
          constructor
          . by_contra h
            linarith
          . by_contra h
            linarith
        . simp
          refine ⟨?_, ?_, ?_⟩
          . by_contra h
            linarith
          . by_contra h
            linarith
          . by_contra h
            linarith

  · intro h
    rw [h]
    have : {x | |abs (x - a) - 3| = 3} = {a - 6, a, a + 6} := by
      ext x
      simp
      constructor
      · intro h
        rw [abs_eq (by norm_num)] at h
        rcases h with h | h
        . have : |x - a| = 6 := by linarith
          rw [abs_eq (by norm_num)] at this
          rcases this with h | h
          . right; right
            linarith
          . left
            linarith
        . have : |x - a| = 0 := by linarith
          rw [abs_eq_zero] at this
          right; left
          linarith

      · intro h
        rcases h with rfl | rfl | rfl
        all_goals simp
        all_goals norm_num

    rw [this]
    rw [Set.encard_insert_of_not_mem]
    rw [Set.encard_pair (by linarith)]
    norm_num

    simp
    by_contra h
    linarith
