import Mathlib

theorem algebra_12087 {a b c d k : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d)
    (h7 : a * k ^ 3 + b * k ^ 2 + c * k + d = 0)
    (h8 : b * k ^ 3 + c * k ^ 2 + d * k + a = 0) :
    k = 1 ∨ k = -1 ∨ k = Complex.I ∨ k = -Complex.I := by
  have h9 : a * k ^ 4 - a = 0 := by
    calc
      a * k ^ 4 - a = a * k ^ 4 + b * k ^ 3 + c * k ^ 2 + d * k - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by ring_nf
      _ = (a * k ^ 3 + b * k ^ 2 + c * k + d) * k - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by ring_nf
      _ = (0) * k - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by rw [h7]
      _ = - (b * k ^ 3 + c * k ^ 2 + d * k + a) := by ring_nf
      _ = - (0) := by rw [h8]
      _ = 0 := by ring_nf
  have h10 : a * (k ^ 4 - 1) = 0 := by
    calc
      a * (k ^ 4 - 1) = a * k ^ 4 - a := by ring_nf
      _ = 0 := by exact h9
  have h11 : k ^ 4 - 1 = 0 := by 
    have h_ne : a ≠ 0 := ha
    apply_fun (λ z => z / a) at h10
    field_simp [h_ne] at h10
    simpa using h10
  have h12 : k ^ 4 = 1 := by 
    calc
      k ^ 4 = k ^ 4 - 1 + 1 := by ring_nf
      _ = 0 + 1 := by rw [h11]
      _ = 1 := by ring_nf
  have h13 : (k - 1) * (k + 1) * (k - Complex.I) * (k + Complex.I) = 0 := by
    have h14 : k ^ 4 - 1 = 0 := h11
    have h15 : k ^ 4 - 1 = (k - 1) * (k + 1) * (k - Complex.I) * (k + Complex.I) := by
      ring_nf
      simp [Complex.I_mul_I]
      <;> ring_nf
    rw [h15] at h14
    exact h14
  cases' (mul_eq_zero.mp h13) with h14 h15
  · cases' (mul_eq_zero.mp h14) with h16 h17
    · cases' (mul_eq_zero.mp h16) with h18 h19
      · -- Case k - 1 = 0, so k = 1
        left
        exact eq_of_sub_eq_zero h18
      · -- Case k + 1 = 0, so k = -1
        right
        left
        have h20 : k = -1 := by
          have : k + 1 = 0 := h19
          calc
            k = (k + 1) - 1 := by ring_nf
            _ = (0) - 1 := by rw [this]
            _ = -1 := by ring_nf
        exact h20
    · -- Case k - I = 0, so k = I
      right
      right
      left
      exact eq_of_sub_eq_zero h17
  · -- Case k + I = 0, so k = -I
    right
    right
    right
    have h21 : k = -Complex.I := by
      have : k + Complex.I = 0 := h15
      calc
        k = (k + Complex.I) - Complex.I := by ring_nf
        _ = (0) - Complex.I := by rw [this]
        _ = -Complex.I := by ring_nf
    exact h21