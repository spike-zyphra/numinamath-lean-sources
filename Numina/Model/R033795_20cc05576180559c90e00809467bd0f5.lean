import Mathlib

theorem number_theory_7018 (x p : ℤ) (hp : Prime p) (h : x ^ 2 + 1 = 2 * p) :
    p ≡ 1 [ZMOD 4] := by

  have h1 : x % 2 = 1 := by
    by_contra h2
    have h2 : x % 2 = 0 := by omega
    have h4 : (x : ℤ) % 2 = 0 := by omega
    have h5 : x ^ 2 % 2 = 0 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h4]
    have h6 : (2 * p) % 2 = 0 := by
      omega
    have h7 : (x ^ 2 + 1) % 2 = 1 := by
      omega
    omega

  have h2 : ∃ k : ℤ, x = 2 * k + 1 := by
    refine' ⟨(x - 1) / 2, by omega⟩

  rcases h2 with ⟨k, hk⟩

  have eq1 : (2 * k + 1 : ℤ) ^ 2 + 1 = 2 * p := by
    rw [hk] at h
    all_goals nlinarith

  have eq2 : p = 2 * k^2 + 2 * k + 1 := by 
    nlinarith

  have eq3 : p % 4 = 1 := by 
    have eq4 : p = 2 * (k^2 + k) + 1 := by
      nlinarith
    have eq5 : (k^2 + k : ℤ) % 2 = 0 := by 
      have eq6 : k * (k + 1) % 2 = 0 := by
        have h1 : k % 2 = 0 ∨ k % 2 = 1 := by
          omega
        rcases h1 with (h1 | h1)
        · 
          simp [Int.add_emod, Int.mul_emod, h1]
        · 
          simp [Int.add_emod, Int.mul_emod, h1]
      have eq7 : (k^2 + k : ℤ) % 2 = 0 := by
        have eq8 : k^2 + k = k * (k + 1) := by
          ring
        rw [eq8]
        omega
      omega
    omega

  simp [Int.ModEq]
  omega