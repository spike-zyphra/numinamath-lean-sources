import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_318344 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IsLeast {x | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ x = max (max a b) ((1 / a ^ 2) + (1 / b ^ 2))} (2 ^ ((1 : ℝ) / 3)) := by 
  constructor
  · -- Show that 2^(1/3) is in the set.
    use (2: ℝ) ^ ((1: ℝ) / 3), (2: ℝ) ^ ((1: ℝ) / 3)
    constructor
    · positivity
    constructor
    · positivity
    · -- Show that 2^(1/3) = max (max a b) (1/a^2 + 1/b^2) when a = b = 2^(1/3)
      have h1 : (2 : ℝ) ^ ((1 : ℝ) / 3) = (2 : ℝ) ^ ((1 : ℝ) / 3) := by rfl
      have h2 : ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
        calc
          ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 = (2 : ℝ) ^ (2 * ( (1 : ℝ) / 3 ) ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; norm_num; all_goals linarith
          _ = (2 : ℝ) ^ ((2 : ℝ) / 3) := by ring_nf
      have h3 : (1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) + (1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
        have h4 : (1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) + (1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) = 2 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) := by
          have h2' : ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / 3) := h2
          rw [show (1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) + (1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) = 2 * (1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2) by ring]
          field_simp [h2']
          all_goals nlinarith
        rw [h4]
        have h5 : (2 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) ) = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
          field_simp [← Real.rpow_add, ← Real.rpow_natCast]
          <;> ring_nf
        rw [h5]
      have h6 : max (max ((2 : ℝ) ^ ((1 : ℝ) / 3)) ((2 : ℝ) ^ ((1 : ℝ) / 3)) ) ((1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 2 ) + (1 / ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 )) = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [show max ((2 : ℝ) ^ ((1 : ℝ) / 3)) ((2 : ℝ) ^ ((1 : ℝ) / 3)) = (2 : ℝ) ^ ((1 : ℝ) / 3) by
          simp
        ]
        rw [h3]
        all_goals
          norm_num [h3]
      linarith [h6]
  · -- Show that 2^(1/3) is the least element of the set.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩
    by_contra h
    push_neg at h
    rw [show x = max (max a b) ((1 / a ^ 2) + (1 / b ^ 2)) by linarith] at h
    have h1 : max (max a b) ((1 / a ^ 2) + (1 / b ^ 2)) < (2 : ℝ) ^ ((1 : ℝ) / 3) := by
      linarith
    have h2 : a < (2 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h3 : max (max a b) ((1 / a ^ 2) + (1 / b ^ 2)) ≥ a := by
        simp [max_le_iff]
      linarith [h3, h1]
    have h3 : b < (2 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h4 : max (max a b) ((1 / a ^ 2) + (1 / b ^ 2)) ≥ b := by
        simp [max_le_iff]
      linarith [h4, h1]
    have h4 : a ^ 2 < (2 : ℝ) ^ ((2 : ℝ) / 3) := by
      have h3' : a < (2 : ℝ) ^ ((1 : ℝ) / 3) := h2
      have h8 : a ^ 2 < (((2 : ℝ) ^ ((1 : ℝ) / 3)) ) ^ 2 := by
        nlinarith [show 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) by positivity, Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 3), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 3)]
      have h7 : (((2 : ℝ) ^ ((1 : ℝ) / 3)) ) ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
        calc
          ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (2 : ℝ) ^ (2 * ( (1 : ℝ) / 3 ) ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; norm_num; all_goals linarith
          _ = (2 : ℝ) ^ ((2 : ℝ) / 3) := by ring_nf
      linarith [h7]
    have h5 : b ^ 2 < (2 : ℝ) ^ ((2 : ℝ) / 3) := by
      have h4' : b < (2 : ℝ) ^ ((1 : ℝ) / 3) := h3
      have h8 : b ^ 2 < (((2 : ℝ) ^ ((1 : ℝ) / 3)) ) ^ 2 := by
        nlinarith [show 0 < (2 : ℝ) ^ ((1 : ℝ) / 3) by positivity, Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 3), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 3)]
      have h7 : (((2 : ℝ) ^ ((1 : ℝ) / 3)) ) ^ 2 = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
        calc
          ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (2 : ℝ) ^ (2 * ( (1 : ℝ) / 3 ) ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; norm_num; all_goals linarith
          _ = (2 : ℝ) ^ ((2 : ℝ) / 3) := by ring_nf
      linarith [h7]
    have h7 : (1 / a ^ 2 + (1 / b ^ 2) ) ≥ (2 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) ) := by
      have h8' : (2 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) ) = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
        field_simp [← Real.rpow_add, ← Real.rpow_natCast]
        <;> ring_nf
      rw [h8']
      have h9 : (1 / a ^ 2) > (1 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) ) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (2 / 3), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 3)]
      have h10 : (1 / b ^ 2) > (1 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) ) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (2 / 3), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 3)]
      have h11 : (1 / a ^ 2) + (1 / b ^ 2) ≥ (2 : ℝ) ^ ((1 : ℝ) / 3) := by
        have h8'' : (1 / a ^ 2 : ℝ) > (1 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) ) := h9
        have h9'' : (1 / b ^ 2 : ℝ) > (1 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) ) := h10
        have h12 : (1 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) ) = (2 : ℝ) ^ ((1 : ℝ) / 3) / 2 := by
          field_simp [← Real.rpow_add, ← Real.rpow_natCast]
          <;> ring_nf
        rw [h12] at h8'' h9''
        have h13 : (1 / a ^ 2 : ℝ) + (1 / b ^ 2) > (2 : ℝ) ^ ((1 : ℝ) / 3) := by
          nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 3)]
        linarith
      linarith [h11, h8']
    have h8 : max (max a b) ((1 / a ^ 2) + (1 / b ^ 2)) ≥ (1 / a ^ 2 + (1 / b ^ 2) ) := by
      simp [max_le_iff]
    linarith [h1, h8, show (2 / ((2 : ℝ) ^ ((2 : ℝ) / 3)) ) = (2 : ℝ) ^ ((1 : ℝ) / 3) by
      field_simp [← Real.rpow_add, ← Real.rpow_natCast]
      <;> ring_nf
    ]