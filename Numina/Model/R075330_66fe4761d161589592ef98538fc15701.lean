import Mathlib

theorem algebra_176019 {a b c d e : ℝ} (h₀ : a + b + 1 = b + c - 2) (h₁ : b + c - 2 = c + d + 3)
    (h₂ : c + d + 3 = d + e - 4) (h₃ : d + e - 4 = e + a + 5) :
    max (max (max (max a b) c) d) e = b := by
  have hc : c = a + 3 := by 
    linarith
  have hd : d = a + 9 := by
    linarith [h₃]
  have hb : b = a + 14 := by
    linarith [h₁, hc, hd]
  have he : e = a + 10 := by 
    linarith [h₂, hc, hd]
  have h1 : b ≥ a := by 
    linarith [hb]
  have h2 : b ≥ c := by 
    linarith [hb, hc]
  have h3 : b ≥ d := by 
    linarith [hb, hd]
  have h4 : b ≥ e := by 
    linarith [hb, he]
  simp [max_eq_left, max_eq_right, h1, h2, h3, h4]
  all_goals linarith