import Mathlib

theorem algebra_131929 (a b c : ℝ) (ha : a ≠ 0) (x : ℕ → ℝ)
    (hx : StrictMono x) (hxi : ∀ i ∈ Finset.range 7, x (i + 1) - x i = x 1 - x 0)
    (y : ℕ → ℝ) (hy : ∀ i ∈ Finset.range 7, y i = a * (x i)^2 + b * x i + c)
    (h : y 0 = 51) (h' : y 1 = 107) (h'' : y 2 = 185) (h''' : y 3 = 285)
    (h'''' : y 4 = 407) (h''''' : y 5 = 549) (h'''''' : y 6 = 717) :
    y 3 = 551 := by
  have eq0 : y 0 = a * (x 0) ^2 + b * x 0 + c := by
    apply hy 0 
    simp
  have eq1 : y 1 = a * (x 1) ^2 + b * x 1 + c := by 
    apply hy 1 
    simp
  have eq2 : y 2 = a * (x 2) ^2 + b * x 2 + c := by
    apply hy 2 
    simp 
  have eq3 : y 3 = a * (x 3) ^2 + b * x 3 + c := by 
    apply hy 3 
    simp
  have eq4 : y 4 = a * (x 4) ^2 + b * x 4 + c := by
    apply hy 4 
    simp 
  have eq5 : y 5 = a * (x 5) ^2 + b * x 5 + c := by 
    apply hy 5 
    simp 
  have eq6 : y 6 = a * (x 6) ^2 + b * x 6 + c := by 
    apply hy 6 
    simp 
  simp [eq0] at h 
  simp [eq1] at h' 
  simp [eq2] at h''
  simp [eq3] at h'''
  simp [eq4] at h''''
  simp [eq5] at h'''''
  simp [eq6] at h''''''
  have eq21 : x 2 - x 1 = x 1 - x 0 := by
    specialize hxi 1 (by norm_num)
    simpa using hxi 
  have eq31 : x 3 - x 2 = x 1 - x 0 := by 
    specialize hxi 2 (by norm_num)
    simpa using hxi 
  have eq41 : x 4 - x 3 = x 1 - x 0 := by 
    specialize hxi 3 (by norm_num)
    simpa using hxi 
  have eq51 : x 5 - x 4 = x 1 - x 0 := by 
    specialize hxi 4 (by norm_num)
    simpa using hxi 
  have eq61 : x 6 - x 5 = x 1 - x 0 := by 
    specialize hxi 5 (by norm_num)
    simpa using hxi 
  have hx2 : x 2 = 2 * x 1 - x 0 := by 
    linarith 
  have hx3 : x 3 = 3 * x 1 - 2 * x 0 := by
    linarith [eq21, eq31]
  have hx4 : x 4 = 4 * x 1 - 3 * x 0 := by 
    linarith [eq31, eq41, hx2, hx3]
  have hx5 : x 5 = 5 * x 1 - 4 * x 0 := by 
    linarith [eq41, eq51, hx3, hx4]
  have hx6 : x 6 = 6 * x 1 - 5 * x 0 := by 
    linarith [eq51, eq61, hx4, hx5]
  rw [hx2] at h''
  rw [hx3] at h'''
  rw [hx4] at h''''
  rw [hx5] at h'''''
  rw [hx6] at h''''''
  have h9 : y 3 = 551 := by 
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact_mod_cast ha), sq_pos_of_pos (show x 1 - x 0 > 0 by 
      have h10 : x 1 > x 0 := by 
        apply hx
        all_goals norm_num 
      linarith 
    ), sq_nonneg (x 1 - x 0), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), 
      hx (show (0 : ℕ) < (1 : ℕ) by norm_num), hx (show (1 : ℕ) < (2 : ℕ) by norm_num), 
      hx (show (2 : ℕ) < (3 : ℕ) by norm_num), hx (show (3 : ℕ) < (4 : ℕ) by norm_num), 
      hx (show (4 : ℕ) < (5 : ℕ) by norm_num), hx (show (5 : ℕ) < (6 : ℕ) by norm_num)
    ]
  linarith [h9, h''']