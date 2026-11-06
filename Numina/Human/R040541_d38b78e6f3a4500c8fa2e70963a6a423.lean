import Mathlib

open Real Set
open scoped Real

/- Find all real numbers $x$ between 0 and 360 such that $\sqrt{3} \cos 10^\circ = \cos 40^\circ + \sin x^\circ.$  Enter all the solutions, separated by commas. -/

theorem calculus_22878' : {x : ℝ | x ∈ Icc 0 360 ∧ sqrt 3 * cos (10 * π / 180) = cos (40 * π / 180) + sin (x * π / 180)} = {70, 110} := by
  ext x
  have pipos : 0 < π := by
    exact pi_pos
  constructor
  · -- if $\sqrt{3} \cos 10^\circ = \cos 40^\circ + \sin x^\circ$ then $x = 70, 110$
    simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff, and_imp]
    intro hx
    rw [mem_Icc] at hx
    -- if the equation holds then $x = 70, 110$
    intro heq
    rw [add_comm] at heq
    apply sub_eq_of_eq_add at heq
    -- $\sqrt{3} = 2\cos 30^\circ$
    have eq1 : √3 = 2 * cos (30 * π / 180) := by
      ring_nf
      field_simp
    rw [eq1] at heq
    -- $\cos(40^\circ) = \cos 10^\circ \cos 30^\circ - \sin 10^\circ \sin 30^\circ$
    have eq2 : cos (40 * π / 180) = cos (10 * π / 180 + 30 * π / 180) := by
      ring_nf
    rw [eq2, cos_add] at heq
    ring_nf at heq
    rw [mul_comm (cos (π * (1 / 6))), ← cos_sub] at heq
    ring_nf at heq
    rw [neg_div, mul_neg, cos_neg, ← sin_pi_div_two_sub] at heq
    ring_nf at heq
    -- $\sin x^\circ = \sin 70^\circ$, so there is $k$ such that $x = 2k\pi + 70^\circ$ or $x = (2k + 1)\pi - 70^\circ$
    rcases Real.sin_eq_sin_iff.mp heq with ⟨k, hk | hk⟩
    · -- if $x = 2k\pi + 70^\circ$, then $k = 0$ and $x = 70^\circ$
      left
      have kge : 0 ≤ k := by
        by_contra contra
        rw [not_le] at contra
        have kle2 : (k : ℝ) ≤ -1 := by
          exact Int.cast_le_neg_one_of_neg contra
        nlinarith
      have kle : k ≤ 0 := by
        by_contra contra
        rw [not_le] at contra
        have kgt : (1 : ℤ) ≤ (k : ℝ) := by
          exact Int.cast_le.mpr contra
        rw [Int.cast_one] at kgt
        nlinarith
      interval_cases k
      field_simp at hk
      nlinarith
    · -- if $x = (2k + 1)\pi - 70^\circ$ then $k = 0$ and $x = 110^\circ$
      right
      have kge : 0 ≤ k := by
          by_contra contra
          rw [not_le] at contra
          have kle2 : (k : ℝ) ≤ -1 := by
            exact Int.cast_le_neg_one_of_neg contra
          nlinarith
      have kle : k ≤ 0 := by
          by_contra contra
          rw [not_le] at contra
          have kgt : (1 : ℤ) ≤ (k : ℝ) := by
            exact Int.cast_le.mpr contra
          rw [Int.cast_one] at kgt
          nlinarith
      interval_cases k
      field_simp at hk
      nlinarith
  · -- if $x = 70, 110$ then $\sqrt{3} \cos 10^\circ = \cos 40^\circ + \sin x^\circ$
    simp only [mem_insert_iff, mem_singleton_iff, mem_Icc, mem_setOf_eq]
    rintro (rfl | rfl)
    · -- if $x = 70$ then $\sqrt{3} \cos 10^\circ = \cos 40^\circ + \sin 70^\circ$
      norm_num
      rw [add_comm]
      apply eq_add_of_sub_eq
      -- $\sqrt{3} = 2\cos 30^\circ$
      have eq1 : √3 = 2 * cos (30 * π / 180) := by
        ring_nf
        field_simp
      rw [eq1]
      -- $\cos(40^\circ) = \cos 10^\circ \cos 30^\circ - \sin 10^\circ \sin 30^\circ$
      have eq2 : cos (40 * π / 180) = cos (10 * π / 180 + 30 * π / 180) := by
        ring_nf
      rw [eq2, cos_add]
      ring_nf
      rw [mul_comm (cos (π * (1 / 6))), ← cos_sub]
      ring_nf
      rw [neg_div, mul_neg, cos_neg, ← sin_pi_div_two_sub]
      ring_nf
    · -- if $x = 110$ then $\sqrt{3} \cos 10^\circ = \cos 40^\circ + \sin 110^\circ$
      norm_num
      rw [add_comm]
      apply eq_add_of_sub_eq
      -- $\sqrt{3} = 2\cos 30^\circ$
      have eq1 : √3 = 2 * cos (30 * π / 180) := by
        ring_nf
        field_simp
      rw [eq1]
      -- $\cos(40^\circ) = \cos 10^\circ \cos 30^\circ - \sin 10^\circ \sin 30^\circ$
      have eq2 : cos (40 * π / 180) = cos (10 * π / 180 + 30 * π / 180) := by
        ring_nf
      rw [eq2, cos_add]
      ring_nf
      rw [mul_comm (cos (π * (1 / 6))), ← cos_sub]
      ring_nf
      rw [neg_div, mul_neg, cos_neg, ← sin_pi_div_two_sub, ← sin_pi_sub]
      ring_nf