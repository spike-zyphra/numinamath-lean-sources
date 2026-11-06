import Mathlib

theorem algebra_285141 {a : ℕ → ℝ} {p q : ℕ} (h : ∃ d, ∀ n, a n = a 0 + d * n)
    (h1 : ∑ i in Finset.range p, a i = q) (h2 : ∑ i in Finset.range q, a i = p) (hp : p ≠ q) :
    ∑ i in Finset.range (p + q), a i = -(p + q) := by
  rcases h with ⟨d, had⟩
  have hp0 : p ≠ 0 := by
    by_contra h4
    have hp0 : p = 0 := by linarith
    rw [hp0] at h1 
    simp at h1 
    have hq0 : q = (0 : ℝ) := by linarith
    have hq0' : q = 0 := by exact_mod_cast hq0
    have h_eq : p = q := by 
      rw [hp0, hq0']
    tauto
  have hq0 : q ≠ 0 := by 
    by_contra h5
    have hq0 : q = 0 := by linarith
    rw [hq0] at h2 
    simp at h2 
    have hp0 : p = (0 : ℝ) := by linarith
    have hp0' : p = 0 := by exact_mod_cast hp0
    have h_eq : p = q := by 
      rw [hp0', hq0]
    tauto
  have h3 : p + q ≠ 0 := by
    omega
  have h_sum : ∀ (n : ℕ), ∑ i in Finset.range n, a i = (n : ℝ) / 2 * (2 * a 0 + (n - 1 : ℝ) * d) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [had n]
      <;> 
      field_simp at *
      <;> 
      ring_nf 
  have eq1 := h_sum p
  have eq2 := h_sum q
  have eq3 := h1
  rw [eq1] at eq3
  have eq4 := h2
  rw [eq2] at eq4
  have eq5 : (p : ℝ) * (2 * a 0 + (p - 1 : ℝ) * d) = 2 * (q : ℝ) := by
    have h4 : (p : ℝ) ≠ 0 := by
      exact_mod_cast hp0
    field_simp at eq3 ⊢
    nlinarith
  have eq6 : (q : ℝ) * (2 * a 0 + (q - 1 : ℝ) * d) = 2 * (p : ℝ) := by
    have h5 : (q : ℝ) ≠ 0 := by
      exact_mod_cast hq0
    field_simp at eq4 ⊢
    nlinarith
  have eq7 : 2 * a 0 + ((p + q - 1 : ℝ)) * d = -2 := by
    have eq8 : (p : ℝ) * (2 * a 0 + (p - 1 : ℝ) * d) = 2 * (q : ℝ) := eq5
    have eq9 : (q : ℝ) * (2 * a 0 + (q - 1 : ℝ) * d) = 2 * (p : ℝ) := eq6
    have eq10 : (p - q : ℝ) * (2 * a 0 + ((p + q - 1 : ℝ)) * d) = -2 * (p - q : ℝ) := by
      ring_nf at eq8 eq9 ⊢
      nlinarith
    have h11 : (p - q : ℝ) ≠ 0 := by
      intro h11
      have h12 : (p : ℝ) = (q : ℝ) := by linarith
      have h13 : p = q := by
        exact_mod_cast h12
      tauto
    have eq11 : 2 * a 0 + ((p + q - 1 : ℝ)) * d = -2 := by
      apply (mul_left_inj' (show (p - q : ℝ) ≠ 0 by 
        exact h11
      )).mp
      linarith
    exact eq11
  have eq8 : ∑ i in Finset.range (p + q), a i = (p + q : ℝ) / 2 * (2 * a 0 + (p + q - 1 : ℝ) * d) := by
    have h9 : ∀ (n : ℕ), ∑ i in Finset.range n, a i = (n : ℝ) / 2 * (2 * a 0 + (n - 1 : ℝ) * d) := h_sum
    specialize h9 (p + q)
    simpa using h9
  rw [eq8]
  rw [eq7]
  field_simp [show (p + q : ℝ) ≠ 0 by exact_mod_cast show p + q ≠ 0 by omega]
  <;> 
  nlinarith