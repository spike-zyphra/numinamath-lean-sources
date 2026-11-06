import Mathlib

theorem algebra_267073 (x : ℂ) (hx : 1 + x + x^2 + x^3 + x^4 = 0) :
    ∑ i ∈ Finset.range 1990, x^i = 0 := by

  have h1 : x ≠ 1 := by 
    intro h
    rw [h] at hx
    norm_num at hx

  have eq1 : x^5 = 1 := by 
    have eq2 : x^5 - 1 = 0 := by
      calc
        x^5 - 1 = (x - 1) * (1 + x + x^2 + x^3 + x^4) := by ring
        _ = (x - 1) * (0) := by rw [hx]
        _ = 0 := by ring
    have eq3 : x^5 - 1 = 0 := eq2
    have eq4 : x^5 = 1 := by
      have h3 : x^5 - 1 = 0 := eq3
      have h4 : x^5 - 1 = x^5 - 1 := by rfl
      have h5 : x^5 = 1 := by 
        have h6 : x^5 - 1 = 0 := h3
        have h7 : x^5 - 1 = 0 := h6
        have h8 : x^5 = 1 := by
          calc 
            x^5 = (x^5 - 1) + 1 := by ring_nf
            _ = 0 + 1 := by rw [h6]
            _ = 1 := by ring_nf
        exact h8
      exact h5
    exact eq4

  have eq2 : x^1990 = 1 := by 
    calc
      x^1990 = (x^5)^398 := by ring_nf
      _ = (1)^398 := by rw [eq1]
      _ = 1 := by norm_num

  have h2 : x - 1 ≠ 0 := by
    intro h3
    apply h1
    have h4 : x = 1 := by
      have h3' : x - 1 = 0 := by simpa using h3
      have h4' : x = 1 := by 
        calc
          x = (x - 1) + 1 := by ring_nf
          _ = 0 + 1 := by rw [h3']
          _ = 1 := by ring_nf
      exact h4'
    exact h4

  have h3 : ∀ n : ℕ, ∑ i ∈ Finset.range n, x^i = (x^n - 1) / (x - 1) := by
    intro n 
    induction n with 
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [h2]
      <;> ring_nf <;> simp [pow_succ, mul_add, mul_assoc] 
      <;> ring

  have h4 : ∑ i ∈ Finset.range 1990, x^i = (x^1990 - 1) / (x - 1) := h3 1990

  rw [h4, eq2]
  field_simp [h2]