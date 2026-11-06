import Mathlib

/-The polynomial $x^6 + ax + b$ is divisible by $x^2 - 2x - 1.$  Find $a + b.$-/
theorem algebra_22553 {a b : ℝ} (h : Polynomial.X ^ 2 - 2 * Polynomial.X - 1 ∣ (Polynomial.X ^ 6 + Polynomial.C a * Polynomial.X + Polynomial.C b)) :
    a + b = -99 := by
  -- set f, g to simplify the expression
  set f : Polynomial ℝ := Polynomial.X ^ 2 - 2 * Polynomial.X - 1 with hf
  set g : Polynomial ℝ := Polynomial.X ^ 6 + Polynomial.C a * Polynomial.X + Polynomial.C b with hg
  -- show that forall x ∈ ℝ, f ∣ g
  replace h (x : ℝ) : Polynomial.eval x f ∣ Polynomial.eval x g := by
    apply Polynomial.eval_dvd
    exact h
  simp [Dvd.dvd] at h
  -- show that u = 1 + √2, v = 1 - √2 are roots of f
  set u : ℝ := 1 + √2 with hu
  set v : ℝ := 1 - √2 with hv
  -- show that f u = 0
  have hfu : Polynomial.eval u f = 0 := by
    simp [hu, hf]
    ring_nf
    rw [Real.sq_sqrt]
    norm_num
    positivity
  -- show that f v = 0
  have hfv : Polynomial.eval v f = 0 := by
    simp [hv, hf]
    ring_nf
    rw [Real.sq_sqrt]
    norm_num
    positivity
  -- show that g u = 0
  have hgu := h u
  rw [hfu] at hgu
  norm_num at hgu
  -- show that g v = 0
  have hgv := h v
  rw [hfv] at hgv
  norm_num at hgv
  -- substitute the expression of g
  simp [hg] at hgu hgv

  clear hfu hfv h hf hg f g
  -- add two equation together
  have eq : (u ^ 6 + v ^ 6) + a * (u + v) + 2 * b = 0 := by linarith only [hgu, hgv]
  -- show that u + v = 2
  have huv : u + v = 2 := by rw [hu, hv]; norm_num
  rw [huv] at eq
  -- show that 2 * (a + b) = - (u ^ 6 + v ^ 6)
  replace eq : 2 * (a + b) = - (u ^ 6 + v ^ 6) := by linarith only [eq]
  clear hgu hgv
  -- show that 2 * (a + b) = - (u ^ 6 + v ^ 6) = -198
  replace eq : 2 * (a + b) = -198 := by
    calc
      2 * (a + b) = - (u ^ 6 + v ^ 6) := by rw [eq]
      _ = - ((1 + √2) ^ 6 + (1 - √2) ^ 6) := by rw [hu, hv]
      _ = - (2 + 30 * (√2) ^ 2 + 30 * (√2) ^ 4 + 2 * (√2) ^ 6) := by ring_nf
      _ = - (2 + 30 * (√2) ^ 2 + 30 * ((√2) ^ 2) ^ 2 + 2 * ((√2) ^ 2) ^ 3) := by ring_nf
      _ = - 198 := by rw [Real.sq_sqrt]; all_goals norm_num
  -- finally get the result
  linarith only [eq]