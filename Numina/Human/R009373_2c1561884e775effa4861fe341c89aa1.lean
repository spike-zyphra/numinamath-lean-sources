import Mathlib

/-Given that two of the roots of the equation \[x^3 - 10x^2 + 55x - c = 0\]have a product of $30,$ compute $c.$-/
theorem algebra_21771 (c : ℝ) (h : ∃ x y, x ≠ y ∧ x^3-10*x^2+55*x-c=0 ∧ y^3-10*y^2+55*y-c=0 ∧ x*y=30) :
    c=150 := by
  obtain ⟨x, y, hd, hx, hy, hxy⟩ := h
  -- show the vieta formula that x + y + z = 10, xy + yz + zx = 55, xyz = c
  have vieta_formula_cubic : ∃ z, z ^ 3 - 10 * z ^ 2 + 55 * z - c = 0 ∧ x + y + z = 10 ∧ x * y + y * z + z * x = 55 ∧ x * y * z = c := by
    -- substitute c with c = x ^ 3 - 10 * x ^ 2 + 55 * x
    have eq₁ : (y ^ 3 - 10 * y ^ 2 + 55 * y) - (x ^ 3 - 10 * x ^ 2 + 55 * x) = 0 := by
      calc
        (y ^ 3 - 10 * y ^ 2 + 55 * y) - (x ^ 3 - 10 * x ^ 2 + 55 * x) = (y ^ 3 - 10 * y ^ 2 + 55 * y - c) - (x ^ 3 - 10 * x ^ 2 + 55 * x - c) := by ring_nf
        _ = 0 := by rw [hx, hy]; norm_num
    replace eq₁ : (y - x) * (y * y - (10 - x) * y + (x ^ 2 - 10 * x + 55)) = 0 := by
      ring_nf at eq₁ ⊢
      exact eq₁
    -- show that y * y - (10 - x) * y + (x ^ 2 - 10 * x + 55) = 0
    rw [mul_eq_zero] at eq₁
    cases eq₁ with 
      -- when y - x = 0
      | inl eq₁ =>
        contrapose! hd
        clear hd
        linarith only [eq₁]
      -- when y * y - (10 - x) * y + (x ^ 2 - 10 * x + 55) = 0
      | inr eq₁ =>
        apply vieta_formula_quadratic at eq₁
        obtain ⟨z, hz, hsum, hprod⟩ := eq₁
        use z
        refine ⟨?_, ?_, ?_, ?_⟩
        -- calculate that z ^ 3 - 10 * z ^ 2 + 55 * z - c = 0
        . calc
            z ^ 3 - 10 * z ^ 2 + 55 * z - c = z ^ 3 - 10 * z ^ 2 + 55 * z - c - (x ^ 3 - 10 * x ^ 2 + 55 * x - c) := by rw[hx]; ring_nf
            _ = (z - x) * (z * z - (10 - x) * z + (x ^ 2 - 10 * x + 55)) := by ring_nf
            _ = 0 := by rw [hz]; norm_num
        -- show that x + y + z = 10
        . linarith only [hsum]
        -- show that xy + yz + zx = 55
        . calc
            x * y + y * z + z * x = x * (y + z) + y * z := by ring_nf
            _ = x * (10 - x) + (x ^ 2 - 10 * x + 55) := by rw [hsum, hprod]
            _ = 55 := by ring_nf
        -- show that xyz = c
        . calc
            x * y * z = x * (y * z) := by ring_nf
            _ = x * (x ^ 2 - 10 * x + 55) := by rw [hprod]
            _ = x ^ 3 - 10 * x ^ 2 + 55 * x - c + c := by ring_nf
            _ = c := by rw [hx]; ring_nf
  
  -- use the vieta_formula
  obtain ⟨z, _, hs1, hs2, hs3⟩ := vieta_formula_cubic
  -- show that z + (x + y) = 25
  have eq₁ : z + (x + y) = 10 := by linarith only [hs1]
  -- show that z * (x + y) = 25
  have eq₂ : z * (x + y) = 25 := by
    calc
      z * (x + y) = (x * y + y * z + z * x) - x * y := by ring_nf
      _ = 25 := by rw [hs2, hxy]; ring_nf
  -- show the equation with root of z and x + y
  have eq (t : ℝ) : (t - z) * (t - (x + y)) = (t - 5) ^ 2 := by
    calc
      (t - z) * (t - (x + y)) = t ^ 2 - (z + (x + y)) * t + z * (x + y) := by ring_nf
      _ = t ^ 2 - 10 * t + 25 := by rw [eq₁, eq₂]
      _ = (t - 5) ^ 2 := by ring_nf
  -- by above, we can show that z = x + y = 5
  replace eq : z = 5 ∧ x + y = 5 := by
    replace eq := eq 5
    norm_num at eq
    cases eq with
    -- when 5 - z = 0
    | inl eq =>
      -- show that z = 5
      replace eq : z = 5 := by linarith only [eq]
      -- show that x + y = 5
      have _ : x + y = 5 := by
        calc
          x + y = (z + (x + y)) - z := by ring_nf
          _ = 5 := by rw [eq₁, eq]; norm_num
      tauto
    -- when 5 - (x + y) = 0
    | inr eq =>
      -- show that x + y = 5
      replace eq : x + y = 5 := by linarith only [eq]
      -- show that z = 5
      have _ : z = 5 := by
        calc
          z = (z + (x + y)) - (x + y) := by ring_nf
          _ = 5 := by rw [eq₁, eq]; norm_num
      tauto
  -- obtain z = 5
  replace eq : z = 5 := by tauto
  -- finally calculation
  calc
    c = x * y * z := by rw [hs3]
    _ = 30 * 5 := by rw [hxy, eq]
    _ = 150 := by norm_num