import Mathlib

theorem algebra_307945 {a b c : ℝ} (h : a ≠ b ∧ b ≠ c ∧ a ≠ c) (h1 : (a + b) / (a - b) = (b + c) / (b - c)) (h2 : (b + c) / (b - c) = (c + a) / (c - a)) :
    a + b + c = 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 0 ∧ 1 / a + 1 / b + 1 / c = 0 := by 
  rcases h with ⟨ha1, hb1, ha2⟩
  have h3 : a - b ≠ 0 := by
    intro h'
    apply ha1
    linarith
  have h4 : b - c ≠ 0 := by
    intro h'
    apply hb1
    linarith
  have h5 : c - a ≠ 0 := by
    intro h'
    apply ha2
    linarith
  have eq1 : (a + b) * (b - c) = (b + c) * (a - b) := by
    have hne1 : a - b ≠ 0 := h3
    have hne2 : b - c ≠ 0 := h4
    field_simp [hne1, hne2] at h1 ⊢
    linarith
  have eq2 : (b + c) * (c - a) = (c + a) * (b - c) := by
    have hne1 : b - c ≠ 0 := h4
    have hne2 : c - a ≠ 0 := h5
    field_simp [hne1, hne2] at h2 ⊢
    linarith
  -- Simplify equation 1 to get $b^2 = ac$
  have eq3 : b ^ 2 = a * c := by
    linarith [eq1]
  -- Simplify equation 2 to get $c^2 = ab$
  have eq4 : c ^ 2 = a * b := by
    linarith [eq2]
  have eq5 : b ^ 3 = a * b * c := by 
    calc
      b ^ 3 = b * (b ^ 2) := by ring
      _ = b * (a * c) := by rw [eq3]
      _ = a * b * c := by ring
  have eq6 : c ^ 3 = a * b * c := by 
    calc
      c ^ 3 = c * (c ^ 2) := by ring
      _ = c * (a * b) := by rw [eq4]
      _ = a * b * c := by ring
  -- From $b^3 = c^3$, we have $b = c$ in real numbers
  have eq7 : b ^ 3 = c ^ 3 := by
    linarith [eq5, eq6]
  -- This implies $b = c$ which contradicts $b ≠ c$
  have eq8 : b = c := by
    have h4 : b ^ 3 = c ^ 3 := eq7
    have h5 : b ^ 3 - c ^ 3 = 0 := by 
      linarith [h4]
    have h6 : (b - c) * (b ^ 2 + b * c + c ^ 2) = 0 := by 
      ring_nf at h5 ⊢
      linarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- b - c = 0 
      linarith 
    · -- b^2 + b * c + c^2 = 0 
      have h9 : (2 * b + c) ^ 2 + 3 * c ^ 2 = 0 := by
        nlinarith 
      have h10 : (2 * b + c) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (2 * b + c), sq_nonneg (c)]
      have h11 : 3 * c ^ 2 = 0 := by 
        nlinarith [sq_nonneg (2 * b + c), sq_nonneg (c)]
      have h12 : c = 0 := by 
        nlinarith 
      have h13 : b = 0 := by 
        nlinarith [h12, h10]
      exfalso
      apply hb1
      linarith
  -- Contradiction with the hypothesis $b \neq c$
  exfalso
  apply hb1
  linarith [eq8]