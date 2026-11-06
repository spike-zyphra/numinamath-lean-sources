import Mathlib

theorem algebra_156797 {a b c d k : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (h1 : a * k ^ 3 + b * k ^ 2 + c * k + d = 0) (h2 : b * k ^ 3 + c * k ^ 2 + d * k + a = 0) :
    k = 1 ∨ k = -1 ∨ k = Complex.I ∨ k = -Complex.I := by
  have eq1 : a * k ^ 4 - a = 0 := by
    calc
      a * k ^ 4 - a = k * (a * k ^ 3 + b * k ^ 2 + c * k + d) - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by ring_nf
      _ = k * (0) - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by rw [h1]
      _ = -(b * k ^ 3 + c * k ^ 2 + d * k + a) := by ring
      _ = -(0) := by rw [h2]
      _ = 0 := by ring
  
  have eq2 : k ^ 4 - 1 = 0 := by 
    have ha1 : a ≠ 0 := by exact ha 
    have h3 : a * (k ^ 4 - 1) = 0 := by 
      calc 
        a * (k ^ 4 - 1) = (a * k ^ 4 - a) := by ring 
        _ = 0 := eq1 
    cases (mul_eq_zero.1 h3) with 
    | inl h => 
      exfalso 
      apply ha 
      exact h 
    | inr h => 
      exact h
  
  have eq3 : k ^ 4 = 1 := by 
    calc 
      k ^ 4 = (k ^ 4 - 1) + 1 := by ring 
      _ = 0 + 1 := by rw [eq2] 
      _ = 1 := by ring

  have h4 : (k - 1) * (k + 1) * (k ^ 2 + 1) = 0 := by 
    have h5 : k ^ 4 - 1 = 0 := by 
      exact eq2 
    have eq4 : k ^ 4 - 1 = (k - 1) * (k + 1) * (k ^ 2 + 1) := by ring 
    rw [eq4] at h5 
    exact h5

  cases' (mul_eq_zero.1 h4) with h5 h6 
  cases' (mul_eq_zero.1 h5) with h7 h8 
  · -- case $k - 1 = 0$, so $k = 1$.
    left 
    exact eq_of_sub_eq_zero h7 
  · -- case $k + 1 = 0$, so $k = -1$.
    right 
    left 
    have h9 : k = -1 := by 
      have h10 : k + 1 = 0 := h8 
      calc 
        k = k + 1 - 1 := by ring 
        _ = 0 - 1 := by rw [h10] 
        _ = -1 := by ring 
    exact h9 
  · -- case $k^2 + 1 = 0$
    have h10 : k ^ 2 + 1 = 0 := by 
      exact h6 
    have h11 : k ^ 2 + 1 = (k - Complex.I) * (k + Complex.I) := by 
      ring_nf 
      simp [Complex.I_mul_I] 
      <;> ring 
    rw [h11] at h10 
    cases' (mul_eq_zero.1 h10) with h12 h13 
    · -- case $k - i = 0$, so $k = i$.
      right 
      right 
      left 
      exact eq_of_sub_eq_zero h12 
    · -- case $k + i = 0$, so $k = -i$.
      right 
      right 
      right 
      have h14 : k = -Complex.I := by 
        have h15 : k + Complex.I = 0 := h13 
        calc 
          k = k + Complex.I - Complex.I := by ring 
          _ = 0 - Complex.I := by rw [h15] 
          _ = -Complex.I := by ring 
      exact h14