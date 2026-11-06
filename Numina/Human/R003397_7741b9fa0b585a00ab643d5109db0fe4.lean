import Mathlib

open Real Set

theorem algebra_175903 {a m : ℝ}
    (A B C : Set ℝ)
    (hA : A = {x | x^2 - 3 * x + 2 = 0})
    (hB : B = {x | x^2 - a * x + (a - 1) = 0})
    (hC : C = {x | x^2 - m * x + 2 = 0})
    (h1 : A ∪ B = A) (h2 : A ∩ C = C) :
    (a = 2 ∨ a = 3) ∧ (m ∈ Ioo (-2*√2) (2*√2) ∨ m = 3) := by

  simp at h1 h2

  replace hA : A = {1, 2} := by
    rw [hA]
    ext x
    simp
    constructor
    . intro h
      have : (x-1)*(x-2) = 0 := by
        ring_nf
        rw [← h]
        ring_nf
      simp at this
      rcases this with h1 | h2
      . left; linarith
      . right; linarith
    . intro h
      rcases h with rfl | rfl
      . ring_nf
      . ring_nf

  replace hB : B = {1, a-1} := by
    rw [hB]
    ext x
    simp
    constructor
    . intro h
      have : (x-1)*(x-(a-1)) = 0 := by
        ring_nf
        rw [← h]
        ring_nf
      simp at this
      rcases this with h1 | h2
      . left; linarith
      . right; linarith
    . intro h
      rcases h with rfl | rfl
      . ring_nf
      . ring_nf

  subst A B

  have ha : (a = 2 ∨ a = 3) := by
    have : a - 1 ∈ ({1, a-1}:Set ℝ) := by
      simp

    have := h1 this
    rcases this with h1 | h2
    . left; linarith
    . right; simp at h2; linarith

  have hm : m ∈ Ioo (-2*√2) (2*√2) ∨ m = 3 := by
    by_contra h
    simp at h
    have ⟨h, h0⟩ := h

    have : 8 ≤ m^2 := by
      have : 8 = (2*√2)^2 := by
        ring_nf
        rw [sq_sqrt (by linarith)]
        norm_num

      rw [this]
      rw [sq_le_sq]
      have : 2*√2 ≥ 0 := by positivity
      rw [abs_of_nonneg this]
      by_cases hm: -(2 * √2) < m
      . have := h hm
        rw [abs_of_pos (by linarith)]
        exact this
      . simp at hm
        rw [abs_of_neg (by nlinarith)]
        linarith

    replace hC : C = {m/2-√(m^2-8)/2, m/2+√(m^2-8)/2} := by
      rw [hC]
      ext x
      simp
      constructor
      . intro h
        have : (x-(m/2-√(m^2-8)/2))*(x-(m/2+√(m^2-8)/2)) = 0 := by
          ring_nf
          rw [sq_sqrt (by linarith)]
          rw [← h]
          ring_nf

        simp at this
        rcases this with h1 | h2
        . left; linarith
        . right; linarith
      . intro h
        rcases h with rfl | rfl
        . ring_nf
          rw [sq_sqrt (by linarith)]
          ring_nf
        . ring_nf
          rw [sq_sqrt (by linarith)]
          ring_nf

    subst C

    have : m/2-√(m^2-8)/2 ∈ ({m/2-√(m^2-8)/2, m/2+√(m^2-8)/2}:Set ℝ) := by
      simp

    have := h2 this
    rcases this with h11 | h12
    . have : √(m ^ 2 - 8) = m - 2 := by linarith
      rw [sqrt_eq_cases] at this
      ring_nf at this
      rcases this with ⟨h3, h4⟩ | h5
      . have : m = 3 := by linarith
        contradiction
      . linarith

    . simp at h12
      have : √(m ^ 2 - 8) ≥ 0 := by positivity
      have : √(m ^ 2 - 8) = m - 4 := by linarith
      rw [sqrt_eq_cases] at this
      ring_nf at this
      rcases this with ⟨h1, h2⟩ | h3
      . linarith
      . linarith

  exact ⟨ha, hm⟩
