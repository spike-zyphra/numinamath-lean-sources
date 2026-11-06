import Mathlib

/-[ Polynomial division with remainder. GCD and LCM of polynomials ]

Prove that if the equations $x^{3}+p x+q=0, x^{3}+p^{\prime} x+q^{\prime}=0$ have a common root, then $\left(p q^{\prime}-q p^{\prime}\right)\left(p-p^{\prime}\right)^{2}=(q-$ $\left.q^{\prime}\right)^{3}$.-/
theorem algebra_220110 {p q p' q' : ℝ} (f g : ℝ → ℝ)
    (hf : f = fun x => x^3 + p * x + q) (hg : g = fun x => x^3 + p' * x + q')
    (hfg : ∃ x, f x = 0 ∧ g x = 0) :
    (p * q' - q * p') * (p - p')^2 = (q - q')^3 := by
  rcases hfg with ⟨x, hfx, hgx⟩
  have eq1 : x^3 + p * x + q = 0 := by
    rw [hf] at hfx
    exact hfx
  have eq2 : x^3 + p' * x + q' = 0 := by
    rw [hg] at hgx
    exact hgx
  have h_subtract : (p - p') * x = q' - q := by linarith
  have eq3 : (q' - q) * x^3 + (p * q' - p' * q) * x = 0 := by
    have eq1' : x^3 + p * x + q = 0 := eq1
    have eq2' : x^3 + p' * x + q' = 0 := eq2
    have h1 : q' * x^3 + p * q' * x + q * q' = 0 := by
      have eq1q' : (x^3 + p * x + q) * q' = 0 := by
        rw [eq1']
        ring
      linarith [eq1q']
    have h2 : q * x^3 + p' * q * x + q * q' = 0 := by
      have eq2q : (x^3 + p' * x + q') * q = 0 := by
        rw [eq2']
        ring
      linarith [eq2q]
    nlinarith [h1, h2]
  by_cases hx : x = 0
  · -- If x = 0, then from eq1 we have q = 0, and from eq2 we have q' = 0
    rw [hx] at eq1 eq2
    have hq : q = 0 := by linarith
    have hq' : q' = 0 := by linarith
    rw [hq, hq']
    ring
  · -- If x ≠ 0, we can divide the equation by x
    have hx' : x ≠ 0 := by
      exact hx
    have h_eq : (q' - q) * x^2 + (p * q' - p' * q) = 0 := by
      have h : x ≠ 0 := hx'
      have eq3' : (q' - q) * x^3 + (p * q' - p' * q) * x = 0 := eq3
      have : x * ((q' - q) * x^2 + (p * q' - p' * q)) = 0 := by
        linarith
      cases (mul_eq_zero.mp this) with
      | inl h1 => contradiction
      | inr h2 => linarith
    by_cases hq : q' - q = 0
    · -- If q' - q = 0, then from h_subtract we have (p - p') * x = 0
      have h2 : (p - p') * x = 0 := by linarith [h_subtract, hq]
      have hp : p - p' = 0 := by
        apply_fun (λ y => y / x) at h2
        field_simp [hx'] at h2
        linarith
      have hp' : p = p' := by linarith
      have hq' : q' = q := by linarith
      rw [hp', hq']
      ring
    · -- If q' - q ≠ 0, then we can proceed
      have h2 : q' - q ≠ 0 := by
        exact hq
      have h3 : p - p' ≠ 0 := by
        by_contra h
        rw [h] at h_subtract
        have : (q' - q) = 0 := by linarith [h_subtract, sq_nonneg x]
        contradiction
      have hx_eq : x = (q' - q) / (p - p') := by
        have h4 : (p - p') * x = q' - q := h_subtract
        field_simp [h3]
        linarith
      have h4 : (q' - q) * ((q' - q) / (p - p'))^2 + (p * q' - p' * q) = 0 := by
        rw [hx_eq] at h_eq
        exact h_eq
      have h5 : (q' - q)^3 + (p * q' - p' * q) * (p - p')^2 = 0 := by
        have h4' : (q' - q) * ((q' - q) / (p - p'))^2 + (p * q' - p' * q) = 0 := h4
        have h6 : (p - p') ≠ 0 := h3
        have h7 : (q' - q)^3 + (p * q' - p' * q) * (p - p')^2 = 0 := by
          have h8 : ((q' - q) / (p - p'))^2 = (q' - q)^2 / (p - p')^2 := by
            field_simp [h6]
          rw [h8] at h4'
          have h9 : (q' - q) * ((q' - q)^2 / (p - p')^2) + (p * q' - p' * q) = 0 := by linarith
          have h10 : (q' - q)^3 + (p * q' - p' * q) * (p - p')^2 = 0 := by
            have h11 : (p - p')^2 ≠ 0 := by
              exact pow_ne_zero 2 h6
            have eq1 : (q' - q)^3 + (p * q' - p' * q) * (p - p')^2 = ((q' - q) * ((q' - q)^2 / (p - p')^2) + (p * q' - p' * q)) * (p - p')^2 := by
              field_simp [h6]
              ring
            rw [eq1]
            have h12 : ((q' - q) * ((q' - q)^2 / (p - p')^2) + (p * q' - p' * q)) = 0 := by linarith [h9]
            rw [h12]
            ring
          linarith [h10]
        linarith [h7]
      have : (p * q' - q * p') * (p - p')^2 = (q - q')^3 := by
        have h13 : (q' - q)^3 + (p * q' - p' * q) * (p - p')^2 = 0 := h5
        nlinarith [sq_nonneg (q' - q), sq_nonneg (p - p')]
      linarith