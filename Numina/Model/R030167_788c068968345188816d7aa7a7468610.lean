import Mathlib

theorem algebra_234897 {x y z n m w : ℕ}
    (h₁ : (x / y : ℝ) = 3 / 4 ∧ (y / z : ℝ) = 4 / 6)
    (h₂ : (n / m : ℝ) = 2 / 5 ∧ (m / w : ℝ) = 5 / 8)
    (h₃ : x - n ≤ 10) (h₄ : (w / z : ℝ) = 1.8) :
    x + y + z = 260 := by
  have h1 := h₁.1
  have h2 := h₁.2
  have h3 := h₂.1
  have h4 := h₂.2
  have eq1 : y ≠ 0 := by
    by_contra h
    rw [show (y : ℝ) = 0 by exact_mod_cast (show (y : ℝ) = (0 : ℝ) by exact_mod_cast h)] at h1
    norm_num at h1
  have eq2 : z ≠ 0 := by
    by_contra h
    rw [show (z : ℝ) = 0 by exact_mod_cast (show (z : ℝ) = (0 : ℝ) by exact_mod_cast h)] at h2
    norm_num at h2
  have eq3 : m ≠ 0 := by
    by_contra h
    rw [show (m : ℝ) = 0 by exact_mod_cast (show (m : ℝ) = (0 : ℝ) by exact_mod_cast h)] at h3
    norm_num at h3
  have eq4 : w ≠ 0 := by
    by_contra h
    rw [show (w : ℝ) = 0 by exact_mod_cast (show (w : ℝ) = (0 : ℝ) by exact_mod_cast h)] at h4
    norm_num at h4
  have h1' : (x : ℝ) * (4 : ℝ) = (y : ℝ) * (3 : ℝ) := by
    have h11 : (y : ℝ) ≠ 0 := by exact_mod_cast show y ≠ 0 by exact eq1
    field_simp at h1 ⊢
    nlinarith
  have h1'' : (x : ℕ) * 4 = (y : ℕ) * 3 := by
    exact_mod_cast h1'
  have h2' : (y : ℝ) * (6 : ℝ) = (z : ℝ) * (4 : ℝ) := by
    have h22 : (z : ℝ) ≠ 0 := by exact_mod_cast show z ≠ 0 by exact eq2
    field_simp at h2 ⊢
    nlinarith
  have h2'' : (y : ℕ) * 6 = (z : ℕ) * 4 := by
    exact_mod_cast h2'
  have h₄' : (w : ℝ) = 1.8 * (z : ℝ) := by
    have h₄₄ : (z : ℝ) ≠ 0 := by exact_mod_cast show z ≠ 0 by exact eq2
    field_simp at h₄ ⊢
    linarith
  have h₄'' : (w : ℝ) = (18 / 10 : ℝ) * (z : ℝ) := by
    rw [h₄']
    norm_num
  have h₄''' : 10 * (w : ℝ) = 18 * (z : ℝ) := by
    nlinarith
  have h₄'''' : 10 * (w : ℕ) = 18 * (z : ℕ) := by
    exact_mod_cast h₄'''
  have h₄''''' : 5 * (w : ℕ) = 9 * (z : ℕ) := by
    omega
  have h₃' : (n : ℝ) * 5 = (m : ℝ) * 2 := by
    have h₃₃ : (m : ℝ) ≠ 0 := by exact_mod_cast show m ≠ 0 by exact eq3
    field_simp at h3 ⊢
    nlinarith
  have h₃'' : (n : ℕ) * 5 = (m : ℕ) * 2 := by
    exact_mod_cast h₃'
  have h₄'''''' : (m : ℝ) * 8 = (w : ℝ) * 5 := by
    have h₄'''' : (w : ℝ) ≠ 0 := by exact_mod_cast show w ≠ 0 by exact eq4
    field_simp at h4 ⊢
    nlinarith
  have h₄'''''' : (m : ℕ) * 8 = (w : ℕ) * 5 := by
    exact_mod_cast h₄'''''' 
  all_goals
    omega