import Mathlib

theorem algebra_94615 (a b c : ℤ) (f : ℤ → ℤ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c)
    (h1 : f 1 = 0) (h2 : f 7 ∈ Set.Ioo 50 60) (h3 : f 8 ∈ Set.Ioo 70 80)
    {k : ℤ} (h4 : f 100 ∈ Set.Ioo (5000 * k) (5000 * (k + 1))) :
    k = 3 := by
  have eq1 : a + b + c = 0 := by
    rw [hf 1] at h1 
    linarith
  have h71 : 50 < a * 7 ^ 2 + b * 7 + c := by
    rw [hf 7] at h2 
    exact h2.1
  have h72 : a * 7 ^ 2 + b * 7 + c < 60 := by 
    rw [hf 7] at h2 
    exact h2.2
  have h81 : 70 < a * 8 ^ 2 + b * 8 + c := by 
    rw [hf 8] at h3 
    exact h3.1 
  have h82 : a * 8 ^ 2 + b * 8 + c < 80 := by 
    rw [hf 8] at h3 
    exact h3.2
  have h1001 : 5000 * k < a * 100 ^ 2 + b * 100 + c := by 
    rw [hf 100] at h4 
    exact h4.1 
  have h1002 : a * 100 ^ 2 + b * 100 + c < 5000 * (k + 1) := by 
    rw [hf 100] at h4 
    exact h4.2
  have eq7 : a * 7 ^ 2 + b * 7 + c = 48 * a + 6 * b := by 
    have h7c : c = -a - b := by linarith [eq1]
    rw [h7c]
    ring 
  rw [eq7] at h71 h72 
  have eq8 : a * 8 ^ 2 + b * 8 + c = 63 * a + 7 * b := by 
    have h8c : c = -a - b := by linarith [eq1]
    rw [h8c]
    ring 
  rw [eq8] at h81 h82 
  have ha : a = 2 := by 
    omega
  have hb : b = -7 := by 
    omega
  have hc : c = 5 := by 
    omega 
  have h100 : a * 100 ^ 2 + b * 100 + c = 19305 := by 
    rw [ha, hb, hc]
    norm_num
  rw [h100] at h1001 h1002 
  omega