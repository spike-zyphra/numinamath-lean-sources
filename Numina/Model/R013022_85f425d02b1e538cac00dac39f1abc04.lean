import Mathlib

open Real
open scoped BigOperators

theorem inequalities_269286 :
  Set.ncard {p : ℤ × ℤ | (|p.1| - 1)^2 + (|p.2| - 1)^2 < 2} = 16 := by
  have h1 : {p : ℤ × ℤ | (|p.1| - 1)^2 + (|p.2| - 1)^2 < 2} = Finset.filter (fun p : ℤ × ℤ => (|p.1| - 1)^2 + (|p.2| - 1)^2 < 2) (Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h2 : x ≤ 2 := by
      by_contra h2
      push_neg at h2
      have h3 : |x| ≥ 3 := by
        rw [abs_of_pos (show 0 < x by omega)]
        omega
      have h4 : (|x| - 1) ^ 2 ≥ 4 := by
        nlinarith
      have h5 : (|y| - 1) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
    have h3 : x ≥ -2 := by
      by_contra h3
      push_neg at h3
      have h4 : |x| ≥ 3 := by
        rw [abs_of_neg (show x < 0 by omega)]
        omega
      have h5 : (|x| - 1) ^ 2 ≥ 4 := by
        nlinarith
      have h6 : (|y| - 1) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
    have h4 : y ≤ 2 := by
      by_contra h4
      push_neg at h4
      have h5 : |y| ≥ 3 := by
        rw [abs_of_pos (show 0 < y by omega)]
        omega
      have h6 : (|y| - 1) ^ 2 ≥ 4 := by
        nlinarith
      have h7 : (|x| - 1) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
    have h5 : y ≥ -2 := by
      by_contra h5
      push_neg at h5
      have h6 : |y| ≥ 3 := by
        rw [abs_of_neg (show y < 0 by omega)]
        omega
      have h7 : (|y| - 1) ^ 2 ≥ 4 := by
        nlinarith
      have h8 : (|x| - 1) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide