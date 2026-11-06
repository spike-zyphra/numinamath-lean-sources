import Mathlib

theorem algebra_220110 {p q p' q' : ℝ} (f g : ℝ → ℝ)
    (hf : f = fun x => x^3 + p * x + q) (hg : g = fun x => x^3 + p' * x + q')
    (hfg : ∃ x, f x = 0 ∧ g x = 0) :
    (p * q' - q * p') * (p - p')^2 = (q - q')^3 := by

  rcases hfg with ⟨a, ha1, ha2⟩

  simp [hf] at ha1
  simp [hg] at ha2

  have eq1 : (p - p') * a + (q - q') = 0 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a + 0), sq_nonneg (a - 0), sq_nonneg (p - p'), sq_nonneg (q - q')]

  by_cases hp : p - p' = 0

  · -- p - p' = 0 
    have h1 : q - q' = 0 := by
      rw [hp] at eq1
      linarith

    have h2 : q = q' := by linarith
    have h3 : p = p' := by linarith

    rw [show q = q' by linarith, show p = p' by linarith]
    all_goals
      ring

  · -- p - p' ≠ 0
    have eq2 : a = (q' - q) / (p - p') := by
      have hne : p - p' ≠ 0 := by
        intro h
        apply hp
        linarith
      field_simp
      linarith

    have eq3 : a^3 + p * a + q = 0 := by
      linarith [ha1]

    rw [eq2] at eq3

    have eq5 : (q' - q)^3 + p * (q' - q) * (p - p')^2 + q * (p - p')^3 = 0 := by
      have hne : p - p' ≠ 0 := by
        intro h
        apply hp
        linarith
      have eq6 : ((q' - q) / (p - p'))^3 + p * ((q' - q) / (p - p')) + q = 0 := by linarith [eq3]
      have eq7 : ((q' - q) / (p - p'))^3 + p * ((q' - q) / (p - p')) + q = 
        ((q' - q)^3 + p * (q' - q) * (p - p')^2 + q * (p - p')^3) / ( (p - p')^3 ) := by 
        field_simp
        <;> ring
      rw [eq7] at eq6 
      have : (q' - q)^3 + p * (q' - q) * (p - p')^2 + q * (p - p')^3 = 0 := by
        field_simp at eq6 ⊢
        <;> nlinarith
      linarith

    nlinarith [sq_nonneg (q' - q), sq_nonneg (p - p'), sq_nonneg (q - q'), sq_nonneg (p * (q' - q)), sq_nonneg (q * (p - p')), sq_nonneg (p - p'), sq_nonneg (q' - q), sq_nonneg (p * (p - p') - p' * (p - p')) ]