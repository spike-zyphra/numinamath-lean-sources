import Mathlib

theorem number_theory_103235 {n : ℤ} (h : Odd (n^2)) : Odd n := by
  have h1 : n % 2 = 1 := by
    by_contra h1
    push_neg at h1
    have h2 : n % 2 = 0 := by
      omega
    have h3 : (n ^ 2) % 2 = 0 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h2]
    have h4 : (n ^ 2) % 2 = 1 := by
      have h5 : Odd (n^2) := h
      rcases h5 with ⟨k, hk⟩
      omega
    omega
  have : Odd n := by 
    refine' ⟨(n - 1) / 2, by 
      omega
    ⟩
  assumption