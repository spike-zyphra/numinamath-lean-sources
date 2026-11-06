import Mathlib

theorem algebra_232707 :
    {d : ℝ | d > 0 ∧ ∃ v1 v2 : ℝ, 15 * v1 = d + 30 ∧ 15 * v2 = d ∧ 60 / v1 = 60 / v2 - 1} = {150} := by 
  ext d 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- If $d \in \{d : \mathbb{R} \mid d > 0 \land \exists v1, v2 : \mathbb{R}, 15 * v1 = d + 30 \land 15 * v2 = d \land 60 / v1 = 60 / v2 - 1\}$, then $d = 150$
    intro h
    rcases h with ⟨hd, v1, v2, h1, h2, h3⟩
    have v1_pos : v1 > 0 := by 
      nlinarith [h1, hd]
    have v2_pos : v2 > 0 := by
      nlinarith [h2, hd]
    have h4 : v1 = (d + 30) / 15 := by 
      linarith
    have h5 : v2 = d / 15 := by 
      linarith
    rw [h4] at h3 
    rw [h5] at h3 
    field_simp [(show (d + 30 : ℝ) ≠ 0 by nlinarith), (show (d : ℝ) ≠ 0 by nlinarith)] at h3 
    ring_nf at h3 
    nlinarith [sq_pos_of_pos hd, h3]
  · -- If $d = 150$, then $d \in \{d : \mathbb{R} \mid d > 0 \land \exists v1, v2 : \mathbb{R}, 15 * v1 = d + 30 \land 15 * v2 = d \land 60 / v1 = 60 / v2 - 1\}$
    intro h
    rw [h]
    constructor
    · norm_num
    · use 12, 10 
      constructor 
      · norm_num 
      constructor
      · norm_num 
      · norm_num