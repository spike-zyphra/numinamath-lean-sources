import Mathlib 

/-- Find all ordered triples $(x, y, z)$ of positive reals such that $x+y+z=27$ and $x^{2}+y^{2}+z^{2}-x y-y z-z x=0$. Prove that your answer is correct.-/
theorem Algebra_611547 {x y z: ℝ} (hx : x > 0) (hy : 0 < y) (hz : 0 < z) 
  (h1 : x + y + z = 27) (h2 : x ^ 2 + y ^ 2 + z ^ 2 -x * y- y * z - z * x = 0) 
  : x = 9 ∧ y = 9 ∧ z = 9 := by 
  -- (x-y)² + (y-z)² + (z-x)² = 0 deduced by the condition above. 
  have eq : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by 
    calc 
      _ = 2 * (x ^ 2 + y ^ 2 + z ^ 2 -x * y- y * z - z * x) := by ring
      _ = 0 := by rw [h2]; simp
  have pos₁ : (x - y) ^ 2 ≥ 0 := by positivity
  have pos₂ : (y - z) ^ 2 ≥ 0 := by positivity
  have pos₃ : (z - x) ^ 2 ≥ 0 := by positivity
  have eq_zero₁ : (x - y) ^ 2 = 0 := by
    apply Eq.symm
    apply eq_iff_le_not_lt.mpr
    constructor
    simpa
    by_contra h
    linarith
  have eq_zero₂ : (y - z) ^ 2 = 0 := by
    apply Eq.symm
    apply eq_iff_le_not_lt.mpr
    constructor
    simpa
    by_contra h
    linarith
  have eq_zero₃ : (z - x) ^ 2 = 0 := by
    apply Eq.symm
    apply eq_iff_le_not_lt.mpr
    constructor
    simpa
    by_contra h
    linarith
  have eq₁ : x - y = 0 := pow_eq_zero eq_zero₁
  have eq₂ : y - z = 0 := pow_eq_zero eq_zero₂
  have eq₃ : z - x = 0 := pow_eq_zero eq_zero₃
  have eq_aux : x = y := by 
    calc 
      _ = x - y + y := by ring
      _ = y := by rw[eq₁]; simp
  have eq_aux' : y = z := by 
    calc 
      _ = y - z + z := by ring
      _ = z := by rw[eq₂]; simp
  rw [←eq_aux', ← eq_aux] at h1
  have x_eq : x = 9 := by 
    calc 
      _ = 3 * x / 3 := by simp
      _ = (x + x + x) / 3 := by 
        ring
      _ = 9 := by rw [h1]; norm_num
  rw [x_eq] at eq_aux
  rw [←eq_aux] at eq_aux'
  exact ⟨x_eq, Eq.symm eq_aux, Eq.symm eq_aux'⟩
