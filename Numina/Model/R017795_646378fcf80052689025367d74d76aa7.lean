import Mathlib

theorem algebra_2847 {a b c x y z : ℝ} (h : x ≠ y ∧ y ≠ z ∧ z ≠ x)
    (f : ℝ → ℝ) (hf : ∀ t, f t = a * t ^ 2 + b * t + c)
    (h1 : f x = y * z) (h2 : f y = x * z) (h3 : f z = x * y) :
    f (x + y + z) = y * z + x * z + x * y := by    
  rcases h with ⟨hx1, hy1, hz1⟩

  have eq1 : a * x ^ 2 + b * x + c = y * z := by
    rw [hf] at h1 
    linarith

  have eq2 : a * y ^ 2 + b * y + c = x * z := by 
    rw [hf] at h2 
    linarith

  have eq3 : a * z ^ 2 + b * z + c = x * y := by 
    rw [hf] at h3 
    linarith

  have eq4 : a * (x ^ 2 - y ^ 2) + b * (x - y) = (y * z - x * z) := by 
    linarith [eq1, eq2]

  have eq1' : (x - y) * (a * (x + y) + b) = -z * (x - y) := by 
    have eq8b : a * (x^2 - y^2) + b * (x - y) = a * (x - y) * (x + y) + b * (x - y) := by
      ring
    have eq5' : a * (x - y) * (x + y) + b * (x - y) = (y * z - x * z) := by
      linarith [eq4, eq8b]
    have h1 : (x - y) * (a * (x + y) + b) = (y * z - x * z) := by
      linarith [eq5']
    have h2 : (y * z - x * z) = -z * (x - y) := by
      ring
    rw [h2] at h1 
    linarith [h1]

  have eq7 : (y - z) * (a * (y + z) + b) = -x * (y - z) := by 
    have eq6b : a * (y ^ 2 - z ^ 2) + b * (y - z) = a * (y - z) * (y + z) + b * (y - z) := by
      ring 
    have eq8b : a * (y ^ 2 - z ^ 2) + b * (y - z) = (x * z - x * y) := by 
      linarith [eq2, eq3]
    have eq9b : a * (y - z) * (y + z) + b * (y - z) = (x * z - x * y) := by 
      linarith [eq6b, eq8b]
    have h1 : (y - z) * (a * (y + z) + b) = (x * z - x * y) := by 
      linarith [eq9b]
    have h2 : (x * z - x * y) = -x * (y - z) := by
      ring 
    rw [h2] at h1 
    linarith [h1]

  have eq10b : (x - z) * (a * (x + z) + b) = -y * (x - z) := by
    have eq6_six : a * (x ^ 2 - z ^ 2) + b * (x - z) = - y * (x - z) := by
      nlinarith [eq1, eq3]
    have eq6' : a * (x ^ 2 - z ^ 2) + b * (x - z) = (x - z) * (a * (x + z) + b) := by
      ring
    linarith [eq6_six, eq6']

  have eq14 : a * (x + y) + b = -z := by
    apply (mul_left_inj' (show x - y ≠ 0 by
      intro h'
      apply hx1
      linarith 
    )).mp 
    linarith [eq1']

  have eq15 : a * (y + z) + b = -x := by 
    apply (mul_left_inj' (show y - z ≠ 0 by
      intro h'
      apply hy1 
      linarith 
    )).mp 
    linarith [eq7]

  have eq16 : a * (x + z) + b = -y := by 
    apply (mul_left_inj' (show x - z ≠ 0 by
      intro h'
      apply hz1 
      linarith 
    )).mp 
    linarith [eq10b]

  -- Let's compute `a` using eq14, eq15, eq16 
  -- By computing from a xt for different variables.
  have eq17 : a = 1 := by 
    have eq24 : (x - z) * (a - 1) = 0 := by 
      nlinarith [eq14, eq15, eq16]
    cases' (mul_eq_zero.mp eq24) with h24 h24'
    · -- x - z = 0
      exfalso 
      apply hz1
      linarith [h24]
    · -- a - 1 = 0
      linarith [h24']

  -- Let's now compute b using eq14 and a = 1
  have eq18 : b = -(x + y + z) := by 
    rw [eq17] at eq14 
    linarith

  -- Let's now compute c using eq1 and a, b
  have eq19 : c = y * z + x * z + x * y := by 
    rw [eq17, eq18] at eq1 
    nlinarith

  have h5 : f (x + y + z) = a * (x + y + z) ^ 2 + b * (x + y + z) + c := hf (x + y + z)
  rw [h5, eq17, eq18, eq19]
  all_goals nlinarith