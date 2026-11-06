import Mathlib

theorem number_theory_275395 (a b c : ℤ) (h₀ : a * b * c % 2 = 1) :
    (a + b + c) % 2 = 1 := by
  have h1 : a % 2 = 1 := by
    by_contra h
    push_neg at h
    have h2 : a % 2 = 0 := by
      omega
    simp [h2, Int.mul_emod, Int.add_emod] at h₀
    all_goals omega

  have h2 : b % 2 = 1 := by
    by_contra h
    push_neg at h
    have h3 : b % 2 = 0 := by
      omega
    simp [h3, Int.mul_emod, Int.add_emod] at h₀
    all_goals omega

  have h3 : c % 2 = 1 := by
    by_contra h
    push_neg at h
    have h4 : c % 2 = 0 := by
      omega
    simp [h4, Int.mul_emod, Int.add_emod] at h₀
    all_goals omega

  simp [Int.add_emod, h1, h2, h3]
  all_goals omega