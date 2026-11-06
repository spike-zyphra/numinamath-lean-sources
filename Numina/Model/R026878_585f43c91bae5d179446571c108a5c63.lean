import Mathlib

theorem number_theory_285857 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : |(x : ℤ) - y| = 58) (h : x^2 ≡ y^2 [ZMOD 100]) :
    min x y = 21 := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx10, hx99⟩
  rcases hy with ⟨hy10, hy99⟩
  have h1 : (x : ℤ) - (y : ℤ) = 58 ∨ (x : ℤ) - (y : ℤ) = -58 := by 
    cases' eq_or_eq_neg_of_abs_eq hxy with h2 h2
    · left 
      linarith 
    · right 
      linarith 
  rcases h1 with h1 | h1 
  · -- Case where x - y = 58, so x = y + 58 
    have h2 : (x : ℤ) = (y : ℤ) + 58 := by linarith 
    rw [Int.ModEq] at h 
    rw [h2] at h 
    norm_num [Int.ModEq] at h 
    have h3 : (y : ℤ) ≥ 10 := by 
      omega 
    have h4 : (y : ℤ) ≤ 41 := by 
      nlinarith 
    interval_cases y <;> omega 
  · -- Case where x - y = -58, so y = x + 58 
    have h2 : (y : ℤ) = (x : ℤ) + 58 := by linarith 
    rw [Int.ModEq] at h 
    rw [h2] at h 
    norm_num [Int.ModEq] at h 
    have h5 : (x : ℤ) ≥ 10 := by 
      omega 
    have h6 : (x : ℤ) ≤ 41 := by 
      nlinarith 
    interval_cases x <;> omega