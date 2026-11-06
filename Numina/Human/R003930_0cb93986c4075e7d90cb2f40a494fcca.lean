import Mathlib

open Real

theorem algebra_223098
  (a : ℝ)
  (S : Set (ℝ × ℝ))
  (hS : S = {(x, y) : ℝ × ℝ | x^2 - y^2 = 0 ∧ (x - a)^2 + y^2 = 1}):
  (S.encard = 2 ↔ a = sqrt 2 ∨ a = -sqrt 2) ∧ (S.encard = 3 ↔ a = 1 ∨ a = -1) := by

  have h_card_0 : a ^ 2 > 2 → S.encard = 0 := by
    intro ha
    suffices S = ∅ by simp; exact this
    ext x
    rw [hS]
    simp
    intro hx
    by_contra h_contra
    have : (x.1 - a / 2) ^ 2 ≥ 0 := by positivity
    linarith

  have h_card_2 : a ^ 2 = 2 → S.encard = 2 := by
    intro ha
    have : S = {(a/2, a/2), (a/2, -a/2)} := by
      ext x
      simp only [hS, Set.mem_setOf_eq]
      constructor
      . intro ⟨hx1, hx2⟩
        have : 2 * (x.1 - a/2) ^ 2 + a ^ 2 / 2 - 1 = 0 := by linarith
        rw [ha] at this
        have : (x.1 - a / 2) ^ 2 = 0 := by linarith
        simp at this
        have hx: x.1 = a / 2 := by linarith

        have : (x.1 - x.2) * (x.1 + x.2) = 0 := by linarith
        simp at this
        rcases this with h1 | h2
        . have hy: x.2 = a / 2 := by linarith
          left; nth_rw 1 [← hx, ← hy]
        . have hy: x.2 = -a / 2 := by linarith
          right; simp; rw [← hx, ← hy]

      . intro hx
        rcases hx with rfl | rfl
        all_goals simp; ring_nf; rw [ha]; norm_num

    rw [this, Set.encard_pair]
    simp
    by_contra h_contra
    have : a = 0 := by linarith
    rw [this] at ha
    norm_num at ha

  have h_card_3 : a ^ 2 = 1 → S.encard = 3 := by
    intro ha
    have : S = {(0, 0), (a, a), (a, -a)} := by
      ext x
      simp only [hS, Set.mem_setOf_eq]
      constructor
      . intro ⟨hx1, hx2⟩
        have : 2 * (x.1 - a/2) ^ 2 + a^2/2 - 1 = 0 := by linarith
        rw [← ha] at this
        have : (x.1 - a/2) ^ 2 = (a/2)^2 := by linarith
        have : (x.1 -a) * x.1 = 0 := by linarith
        simp at this
        rcases this with h1 | h2
        . have ha1 : x.1 = a := by linarith
          rw [ha1] at hx1
          have : (a - x.2) * (a + x.2) = 0 := by linarith
          simp at this
          rcases this with h3 | h4
          . have : x.2 = a := by linarith
            right; left; nth_rw 1 [← ha1, ← this]
          . have : x.2 = -a := by linarith
            right; right; simp; nth_rw 1 [← ha1, ← this]
        . left
          have : x.2 = 0 := by
            rw [h2] at hx1
            have : x.2 ^ 2 = 0 := by linarith
            simp at this; exact this
          nth_rw 1 [← h2, ← this]

      . intro hx
        have : a = 1 ∨ a = -1 := by
          have : (a - 1) * (a + 1) = 0 := by linarith
          simp at this
          rcases this with h1 | h2
          . left; linarith
          . right; linarith
        rcases hx with rfl | rfl | rfl
        all_goals simp; exact this

    rw [this]
    rw [Set.encard_insert_of_not_mem]
    rw [Set.encard_pair]
    norm_num
    . simp
      by_contra h_contra
      have : a = 0 := by linarith
      rw [this] at ha
      norm_num at ha
    . by_contra h_contra
      simp at h_contra

      rcases h_contra with h1 | h2
      . injection h1 with h3 h4
        rw [← h3] at ha
        norm_num at ha
      . injection h2 with h3 h4
        rw [← h3] at ha
        norm_num at ha

  have h_card_4 : (a ^ 2 ≠ 1 ∧ a ^ 2 < 2) → S.encard = 4 := by
    intro ha
    let r1 := a/2-sqrt (2-a^2)/2
    let r2 := a/2+sqrt (2-a^2)/2


    have hr1: (r1 - a) ^ 2 + r1 ^ 2 = 1:= by
      unfold r1
      ring_nf
      rw [sq_sqrt (by linarith)]
      linarith

    have hr2: (r2 - a) ^ 2 + r2 ^ 2 = 1:= by
      unfold r2
      ring_nf
      rw [sq_sqrt (by linarith)]
      linarith

    have hr3: r1 ≠ r2 := by
      by_contra h_contra
      unfold r1 r2 at h_contra
      have : √(2 - a ^ 2) = 0 := by linarith
      rw [sqrt_eq_zero (by linarith)] at this
      have : a ^ 2 = 2 := by linarith
      rw [this] at ha
      norm_num at ha

    have hr4: r1 ≠ 0 ∧ r2 ≠ 0 := by
      by_contra h_contra
      simp at h_contra
      by_cases h : r1 = 0
      . rw [h] at hr1
        have : a ^ 2 = 1 := by linarith
        rw [this] at ha
        norm_num at ha
      . have : r2 = 0 := h_contra h
        rw [this] at hr2
        have : a ^ 2 = 1 := by linarith
        rw [this] at ha
        norm_num at ha

    have : S = {(r1, r1), (r1, -r1), (r2, r2), (r2, -r2)} := by
      ext x
      simp only [hS, Set.mem_setOf_eq]
      constructor
      . intro ⟨hx1, hx2⟩
        have : 2 * (x.1 - a/2) ^ 2 + a^2/2 - 1 = 0 := by linarith
        have : (x.1 - r1) * (x.1 - r2) = 0 := by
          ring_nf
          rw [sq_sqrt (by linarith)]
          linarith

        simp at this
        rcases this with h1 | h2
        . have hx1r1 : x.1 = r1 := by linarith
          rw [hx1r1] at hx1
          have : (r1 - x.2) * (r1 + x.2) = 0 := by linarith
          simp at this
          rcases this with h3 | h4
          . have : x.2 = r1 := by linarith
            left; nth_rw 1 [← hx1r1, ← this]
          . have : x.2 = -r1 := by linarith
            right; left; nth_rw 1 [← hx1r1, ← this]
        . have hx1r2 : x.1 = r2 := by linarith
          rw [hx1r2] at hx1
          have : (r2 - x.2) * (r2 + x.2) = 0 := by linarith
          simp at this
          rcases this with h3 | h4
          . have : x.2 = r2 := by linarith
            right; right; left; nth_rw 1 [← hx1r2, ← this]
          . have : x.2 = -r2 := by linarith
            right; right; right; simp; nth_rw 1 [← hx1r2, ← this]

      . intro hx
        rcases hx with rfl | rfl | rfl | rfl
        all_goals simp; simp only [hr1, hr2]

    rw [this]
    repeat rw [Set.encard_insert_of_not_mem]
    simp; norm_num
    all_goals simp
    . by_contra h_contra
      have : r2 = 0 := by linarith
      exact hr4.2 this
    . constructor
      . intro h
        contradiction
      . exact hr3
    . constructor
      . by_contra h_contra
        have : r1 = 0 := by linarith
        exact hr4.1 this
      . constructor
        . exact hr3
        . intro h
          contradiction

  have h_a_2 : S.encard = 2 → a ^ 2 = 2 := by
    intro h_card
    by_cases ha1: a ^ 2 > 2
    . rw [h_card_0 ha1] at h_card; norm_num at h_card
    . by_contra h_contra
      simp at ha1
      have ha2 : a ^ 2 < 2 := lt_of_le_of_ne ha1 h_contra
      by_cases ha3: a ^ 2 = 1
      . rw [h_card_3 ha3] at h_card; norm_num at h_card
      . rw [h_card_4 ⟨ha3, ha2⟩] at h_card; norm_num at h_card

  have h_a_3 : S.encard = 3 → a ^ 2 = 1 := by
    intro h_card
    by_cases ha1: a ^ 2 > 2
    . rw [h_card_0 ha1] at h_card; norm_num at h_card
    . by_cases ha2: a ^ 2 = 2
      . rw [h_card_2 ha2] at h_card; norm_num at h_card
      . by_contra h_contra
        simp at ha1
        have ha3 : a ^ 2 < 2 := lt_of_le_of_ne ha1 ha2
        rw [h_card_4 ⟨h_contra, ha3⟩] at h_card; norm_num at h_card

  constructor
  . constructor
    . intro h_card
      have : (a - sqrt 2) * (a + sqrt 2) = 0 := by
        ring_nf
        rw [h_a_2 h_card]
        norm_num
      simp at this
      rcases this
      . left; linarith
      . right; linarith
    . intro ha
      rcases ha with rfl | rfl
      all_goals norm_num at h_card_2; exact h_card_2
  . constructor
    . intro h_card
      have : (a - 1) * (a + 1) = 0 := by
        ring_nf
        rw [h_a_3 h_card]
        norm_num
      simp at this
      rcases this
      . left; linarith
      . right; linarith
    . intro ha
      rcases ha with rfl | rfl
      all_goals norm_num at h_card_3; exact h_card_3
