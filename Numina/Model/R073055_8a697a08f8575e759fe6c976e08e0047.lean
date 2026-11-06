import Mathlib

theorem algebra_267381 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (h1 : a 4 + a 7 + a 10 = 17) (h2 : a 4 + a 5 + a 6 + a 7 + a 8 + a 9 + a 10 + a 11 + a 12 + a 13 + a 14 = 77)
    (hk : a k = 13) :
    k = 18 := by
  rcases ha with ⟨d, hd⟩
  have a4 : a 4 = a 0 + d * 4 := hd 4
  have a7 : a 7 = a 0 + d * 7 := hd 7
  have a10 : a 10 = a 0 + d * 10 := hd 10
  have a4' : a 4 = a 0 + d * 4 := hd 4
  have a5 : a 5 = a 0 + d * 5 := hd 5
  have a6 : a 6 = a 0 + d * 6 := hd 6
  have a7' : a 7 = a 0 + d * 7 := hd 7
  have a8 : a 8 = a 0 + d * 8 := hd 8
  have a9 : a 9 = a 0 + d * 9 := hd 9
  have a10' : a 10 = a 0 + d * 10 := hd 10
  have a11 : a 11 = a 0 + d * 11 := hd 11
  have a12 : a 12 = a 0 + d * 12 := hd 12
  have a13 : a 13 = a 0 + d * 13 := hd 13
  have a14 : a 14 = a 0 + d * 14 := hd 14
  have ak : a k = a 0 + d * k := hd k
  rw [a4, a7, a10] at h1
  rw [a4', a5, a6, a7', a8, a9, a10', a11, a12, a13, a14] at h2
  rw [ak] at hk
  have eq3 : 3 * a 0 + 21 * d = 17 := by 
    linarith
  have eq4 : 11 * (a 0 + 9 * d) = 77 := by
    linarith
  have h_a0_d : a 0 + 9 * d = 7 := by 
    linarith
  have h_d : d = 2 / 3 := by
    have h1 : 3 * a 0 + 21 * d = 17 := by 
      linarith
    have h2 : a 0 + 9 * d = 7 := by
      linarith
    have h3 : a 0 = 7 - 9 * d := by
      linarith
    rw [h3] at h1
    linarith
  have h_a0 : a 0 = 1 := by
    have h2 : a 0 + 9 * d = 7 := by
      linarith
    rw [h_d] at h2
    linarith
  rw [h_a0, h_d] at hk
  have hk_eq : (k : ℝ) = 18 := by
    have eq1 : (1 : ℝ) + (2 / 3) * (k : ℝ) = 13 := by
      linarith
    linarith
  have hk_nat : k = 18 := by
    exact_mod_cast hk_eq
  exact hk_nat