import Mathlib

open Real

theorem algebra_297135 (k : ℝ) :
  {x : ℝ | 0 < x ∧ x ≠ 1 ∧ (x^2 + k * x + 3) / (x - 1) = 3 * x + k}.encard = 1
   ↔ k = -33/8 ∨ k = -4 ∨ -3 ≤ k := by

  let S := {x : ℝ | 0 < x ∧ x ≠ 1 ∧ (x ^ 2 + k * x + 3) / (x - 1) = 3 * x + k}
  let T1 := {x : ℝ | 0 < x ∧ x ≠ 1}
  let T2 := {x : ℝ | 2 * x ^ 2 - 3 * x - (3 + k) = 0}

  have hS : T1 ∩ T2 = S := by
    ext x
    unfold T1 T2 S
    simp
    constructor
    . intro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, ?_⟩
      have : x-1 ≠ 0 := by
        by_contra h
        have : x = 1 := by linarith
        contradiction
      field_simp
      linarith
    . intro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      have : x-1 ≠ 0 := by
        by_contra h
        have : x = 1 := by linarith
        contradiction
      field_simp at h3
      linarith

  have hT2a : -33 / 8 ≤ k → T2 = {3 / 4 - √(8 * k + 33) / 4, 3 / 4 + √(8 * k + 33) / 4} := by
    intro hk
    unfold T2
    ext x
    simp
    constructor
    . intro h
      have : 2 * (x - (3 / 4 - √(8 * k + 33) / 4)) * (x - (3 / 4 + √(8 * k + 33) / 4)) = 0 := by
        rw [← h]
        ring_nf
        rw [sq_sqrt (by linarith)]
        ring_nf
      simp at this
      rcases this with h1 | h2
      . left; linarith
      . right; linarith

    . intro h
      rcases h with rfl | rfl
      all_goals
      . ring_nf
        rw [sq_sqrt (by linarith)]
        ring_nf

  have hT2b : k < -33 / 8 → T2 = ∅ := by
    intro hk
    ext x
    unfold T2
    simp
    by_contra h
    have : (x-3/4)^2 ≥ 0 := by positivity
    linarith

  suffices (T1 ∩ T2).encard = 1 ↔ k = -33/8 ∨ k = -4 ∨ -3 ≤ k by
    rw [hS] at this
    unfold S at this
    exact this

  constructor
  . intro h
    rcases lt_trichotomy k (-33 / 8) with hk1 | hk1 | hk1
    . have := hT2b hk1
      rw [this] at h
      simp at h
    . left; exact hk1
    . right
      by_contra hk2
      simp at hk2
      have ⟨ hk2, hk3 ⟩ := hk2
      have := hT2a (by linarith)

      have hT: (T1 ∩ T2) = T2 := by
        simp
        intro x hx
        rw [this] at hx
        unfold T1
        rcases hx with rfl | rfl
        . simp
          constructor
          . suffices √(8 * k + 33) < 3 by linarith
            rw [sqrt_lt (by linarith) (by linarith)]
            linarith

          . by_contra h
            have : √(8 * k + 33) ≥ 0 := by positivity
            linarith

        . simp
          constructor
          . have : √(8 * k + 33) ≥ 0 := by positivity
            linarith
          . by_contra h
            have : √(8 * k + 33) = 1 := by linarith
            rw [sqrt_eq_one] at this
            have : k = -4 := by linarith
            contradiction

      suffices T2.encard = 2 by
        rw [← hT, h] at this
        contradiction

      rw [this]
      rw [Set.encard_pair]
      by_contra h
      have : √(8 * k + 33) = 0 := by linarith
      rw [sqrt_eq_zero (by linarith)] at this
      linarith

  . intro h
    rcases h with rfl | rfl | h
    . ring_nf at hT2a
      simp at hT2a
      have : (T1 ∩ T2) = T2 := by
        simp
        rw [hT2a]
        unfold T1
        simp
        norm_num
      rw [this, hT2a]
      simp
    . ring_nf at hT2a
      have := hT2a (by linarith)
      have : (T1 ∩ T2) = {1/2} := by
        rw [this]
        unfold T1
        ext x
        simp
        constructor
        . intro ⟨⟨h1, h2⟩, h3⟩
          rcases h3 with rfl | rfl
          . norm_num
          . norm_num at h2
        . intro h
          subst x
          simp
          left
          norm_num

      rw [this]
      simp
    . have := hT2a (by linarith)
      have : (T1 ∩ T2) = {3 / 4 + √(8 * k + 33) / 4} := by
        rw [this]
        unfold T1
        ext x
        simp
        constructor
        . intro ⟨⟨h1, h2⟩, h3⟩
          rcases h3 with rfl | rfl
          . have : √(8 * k + 33) < 3 := by linarith
            rw [sqrt_lt (by linarith) (by linarith)] at this
            linarith
          . rfl
        . intro h
          subst x
          refine ⟨⟨?_, ?_⟩, ?_⟩
          . have : √(8 * k + 33) ≥ 0 := by positivity
            linarith
          . by_contra h
            have : √(8 * k + 33) = 1 := by linarith
            rw [sqrt_eq_one] at this
            linarith
          . right; rfl
      rw [this]
      simp
