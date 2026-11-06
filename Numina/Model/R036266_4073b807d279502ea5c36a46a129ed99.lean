import Mathlib

theorem algebra_158317 {x : ℝ} (hx : x^3 - x + 1 = 0) :
    (1 / x)^5 + (1 / x) + 1 = 0 := by
  have h1 : x ≠ 0 := by
    by_contra h
    rw [h] at hx
    nlinarith
  
  have eq1 : x^3 = x - 1 := by linarith
  
  have eq2 : x^4 = x^2 - x := by
    calc
      x^4 = x * x^3 := by ring
      _ = x * (x - 1) := by rw [eq1]
      _ = x^2 - x := by ring
  
  have eq3 : x^5 = -x^2 + x - 1 := by
    calc
      x^5 = x * x^4 := by ring
      _ = x * (x^2 - x) := by rw [eq2]
      _ = x^3 - x^2 := by ring
      _ = (x - 1) - x^2 := by rw [eq1]
      _ = -x^2 + x - 1 := by ring
  
  have h2 : x^5 + x^4 + 1 = 0 := by
    nlinarith [eq1, eq2, eq3]

  have eq4 : (1 / x)^5 + (1 / x) + 1 = (1 + x^4 + x^5) / x^5 := by
    field_simp
    <;> ring
  
  rw [eq4]
  have eq5 : (1 + x^4 + x^5) / x^5 = 0 := by
    have h3 : (1 + x^4 + x^5) = (0 : ℝ) := by 
      nlinarith [h2]
    rw [h3]
    norm_num

  exact eq5