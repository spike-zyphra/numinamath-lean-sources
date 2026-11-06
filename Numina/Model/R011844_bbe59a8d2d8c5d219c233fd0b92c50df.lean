import Mathlib

theorem inequalities_292139 : Set.encard {(x, y) : ℤ × ℤ | (|x| - 1)^2 + (|y| - 1)^2 < 2} = 16 := by 
  have h6 : {(x, y) : ℤ × ℤ | (|x| - 1)^2 + (|y| - 1)^2 < 2} = Finset.filter (fun s : ℤ × ℤ => (|s.1| - 1)^2 + (|s.2| - 1)^2 < 2) (Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2) := by
    ext ⟨x, y⟩
    simp
    intro h 
    have h1 : x ≤ 2 := by 
      by_contra h1
      push_neg at h1
      have h2 : x ≥ 3 := by linarith
      have h3 : |x| ≥ 3 := by
        cases' abs_cases x with h11 h11
        · linarith 
        · linarith
      have h4 : (|x| - 1)^2 ≥ 4 := by 
        nlinarith
      have h5 : (|y| - 1)^2 ≥ 0 := by positivity
      nlinarith
    have h2 : x ≥ -2 := by 
      by_contra h2
      push_neg at h2
      have h3 : x ≤ -3 := by linarith
      have h4 : |x| ≥ 3 := by 
        cases' abs_cases x with h11 h11
        · linarith
        · linarith
      have h5 : (|x| - 1)^2 ≥ 4 := by 
        nlinarith
      have h6 : (|y| - 1)^2 ≥ 0 := by positivity
      nlinarith
    have h3 : y ≤ 2 := by 
      by_contra h3
      push_neg at h3
      have h4 : y ≥ 3 := by linarith
      have h5 : |y| ≥ 3 := by 
        cases' abs_cases y with h11 h11
        · linarith
        · linarith
      have h6 : (|y| - 1)^2 ≥ 4 := by 
        nlinarith
      have h7 : (|x| - 1)^2 ≥ 0 := by positivity
      nlinarith
    have h4 : y ≥ -2 := by 
      by_contra h4
      push_neg at h4
      have h5 : y ≤ -3 := by linarith
      have h6 : |y| ≥ 3 := by 
        cases' abs_cases y with h11 h11
        · linarith
        · linarith
      have h7 : (|y| - 1)^2 ≥ 4 := by 
        nlinarith
      have h8 : (|x| - 1)^2 ≥ 0 := by positivity
      nlinarith
    tauto
  rw [h6]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide