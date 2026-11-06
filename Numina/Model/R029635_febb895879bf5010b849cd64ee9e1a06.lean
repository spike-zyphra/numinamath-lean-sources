import Mathlib

theorem algebra_52377 {f : ℕ → ℕ → ℕ} (hpos : ∀ x y, x > 0 → y > 0 → f x y = f y x)
    (hf : ∀ x y, x > 0 → y > 0 → (x + y) * f x y = y * f x (x + y)) (hf' : ∀ x, x > 0 → f x x = x) :
    f 14 52 = 364 := by
  have h1 : f 2 2 = 2 := hf' 2 (by norm_num)
  have h2 : f 2 4 = 4 := by
    have eq1 := hf 2 2 (by norm_num) (by norm_num)
    simp [show f 2 2 = 2 by linarith [h1]] at eq1
    have eq2 := hpos 2 4 (by norm_num) (by norm_num)
    simp [eq1] at eq2 ⊢
    all_goals omega
  have h3 : f 4 2 = 4 := by
    have h42 := hpos 2 4 (by norm_num) (by norm_num)
    simp [h2] at h42 ⊢
    all_goals omega
  have h4 : f 4 6 = 12 := by
    have eq1 := hf 4 2 (by norm_num) (by norm_num)
    simp [h3] at eq1 ⊢
    all_goals omega
  have h5 : f 4 10 = 20 := by
    have eq1 := hf 4 6 (by norm_num) (by norm_num)
    simp [h4] at eq1 ⊢
    all_goals omega
  have h6 : f 4 14 = 28 := by
    have eq1 := hf 4 10 (by norm_num) (by norm_num)
    simp [h5] at eq1 ⊢
    all_goals omega
  have h7 : f 14 4 = 28 := by
    have h144 : f 14 4 = f 4 14 := hpos 14 4 (by norm_num) (by norm_num)
    omega
  have h8 : f 10 14 = 70 := by
    have eq1 := hf 10 4 (by norm_num) (by norm_num)
    have h104 : f 10 4 = 20 := by
      have h9 : f 10 4 = f 4 10 := hpos 10 4 (by norm_num) (by norm_num)
      omega
    simp [h104] at eq1 ⊢
    all_goals omega
  have h9 : f 14 10 = 70 := by
    have h1410 : f 14 10 = f 10 14 := hpos 14 10 (by norm_num) (by norm_num)
    omega
  have h10 : f 14 24 = 168 := by
    have eq1 := hf 14 10 (by norm_num) (by norm_num)
    simp [h9] at eq1 ⊢
    all_goals omega
  have h11 : f 14 38 = 266 := by
    have eq1 := hf 14 24 (by norm_num) (by norm_num)
    simp [h10] at eq1 ⊢
    all_goals omega
  have h12 : f 14 52 = 364 := by
    have eq1 := hf 14 38 (by norm_num) (by norm_num)
    simp [h11] at eq1 ⊢
    all_goals omega
  exact h12