import Mathlib

def sum (x y : ℤ) := x + y

def ratio (x y : ℤ) := x / (y : ℚ)

def diff (x y : ℤ) := |(x - y)|

theorem algebra_1157 {x y : ℤ} (hr : ratio x y = 5 / 6) (hsum : sum x y = 77) :
    diff x y = 7 := by
  have h1 : (x : ℚ) / (y : ℚ) = (5 : ℚ) / 6 := by 
    unfold ratio at hr
    exact_mod_cast hr
  have h2 : (y : ℚ) ≠ 0 := by
    by_contra h
    rw [h] at h1
    norm_num at h1
  have h3 : 6 * (x : ℚ) = 5 * (y : ℚ) := by
    have hne : (y : ℚ) ≠ 0 := h2
    field_simp [hne] at h1 ⊢
    linarith
  have h4 : 6 * (x : ℤ) = 5 * (y : ℤ) := by
    exact_mod_cast h3
  have h5 : (x : ℤ) + (y : ℤ) = 77 := by 
    unfold sum at hsum
    exact_mod_cast hsum
  have h6 : x = 35 := by 
    omega
  have h7 : y = 42 := by 
    omega
  unfold diff
  rw [h6, h7]
  all_goals norm_num