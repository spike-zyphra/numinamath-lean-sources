import Mathlib

theorem algebra_229085 {p q r x y z : ℝ} (hpqr : p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (h1 : x / p + q / y = 1) (h2 : y / q + r / z = 1) :
    p * q * r + x * y * z = 0 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have h_eq1 : x * y + q * p = p * y := by
    have h11 : p ≠ 0 := hp
    have h12 : y ≠ 0 := hy
    field_simp at h1
    nlinarith
  have h_eq2 : y * z + r * q = q * z := by 
    have h21 : q ≠ 0 := hq
    have h22 : z ≠ 0 := hz
    field_simp at h2 
    nlinarith

  -- From h_eq1: x * y = p * (y - q)
  -- From h_eq2: y * z = q * (z - r)
  have h3 : x * y = p * (y - q) := by
    linarith [h_eq1]
  have h4 : y * z = q * (z - r) := by
    linarith [h_eq2]

  -- To compute p * q * r + x * y * z
  -- First, x * y * z
  -- = (p * (y - q)) * z
  -- = p * z * (y - q)
  -- = p * (y * z - q * z)
  -- = p * (q * (z - r) - q * z)  -- from h4
  -- = p * (q * z - q * r - q * z)
  -- = p * (-q * r)
  -- = -p * q * r
  have h5 : x * y * z = - (p * q * r) := by 
    calc
      x * y * z = (x * y) * z := by ring
      _ = (p * (y - q)) * z := by rw [h3]
      _ = p * z * (y - q) := by ring
      _ = p * ( y * z - q * z ) := by ring
      _ = p * ( (q * (z - r)) - q * z ) := by rw [h4]
      _ = p * ( (q * z - q * r) - q * z ) := by ring
      _ = p * ( -q * r ) := by ring
      _ = - (p * q * r) := by ring
  
  -- Therefore, p * q * r + x * y * z
  -- = p * q * r + ( -p * q * r )
  -- = 0
  linarith [h5]