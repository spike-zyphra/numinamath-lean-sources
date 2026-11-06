import Mathlib

open Complex

lemma norm_mul_exp_arg_mul_I (x : ℂ) : ‖x‖ * exp (arg x * I) = x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    apply Complex.ext <;> field_simp [sin_arg, cos_arg hx, this, mul_comm ‖x‖]

lemma l_norm_eq_one_iff (z : ℂ) : ‖z‖ = 1 ↔ ∃ θ : ℝ, exp (θ * I) = z := by
  refine ⟨fun hz => ⟨arg z, ?_⟩, ?_⟩
  · calc
      exp (arg z * I) = ‖z‖ * exp (arg z * I) := by rw [hz, ofReal_one, one_mul]
      _ = z :=norm_mul_exp_arg_mul_I z
  · rintro ⟨θ, rfl⟩
    exact Complex.norm_exp_ofReal_mul_I θ


theorem Algebra_631431 {z : ℂ} (hz : z ^ 24 = 1 ∧ (z - 1) ^ 510 = 1) :
    z = 1 / 2 + √3 / 2 * I ∨ z = 1 / 2 - (√3 / 2) * I  := by 
  obtain ⟨hz1, hz2⟩ := hz
  have eq1 : Complex.abs (z ^ 24) = abs (1 : ℂ) := by 
    rw [hz1]
  simp at eq1
  have eq3 : abs (z : ℂ) = 1 := by 
    by_cases hge : abs z > 1
    have absge : abs z ^ 24 > 1 ^ 24 := by 
      refine pow_lt_pow_left₀ hge ?_ ?_
      linarith
      linarith
    rw [eq1] at absge
    linarith
    by_cases hle : abs z < 1
    have absle : abs z ^ 24 < 1 ^ 24 := by
      refine pow_lt_pow_left₀ hle ?_ ?_
      positivity
      linarith
    rw [eq1] at absle
    linarith
    linarith
  -- We prove that |z| = 1, so z lies on the unit circle.
  -- use the same method to prove abs (z - 1) = 1
  have eq4 : Complex.abs (z - 1) = 1 := by
    have aux : Complex.abs ((z - 1) ^ 510) = 1 := by 
      rw [hz2]
      simp
    simp at aux
    by_cases hge : Complex.abs (z - 1) > 1
    have absge : Complex.abs (z - 1) ^ 510 > 1 ^ 510 := by
      refine pow_lt_pow_left₀ hge ?_ ?_
      linarith
      linarith
    rw [aux] at absge
    linarith
    by_cases hle : Complex.abs (z - 1) < 1
    have absle : Complex.abs (z - 1) ^ 510 < 1 ^ 510 := by
      refine pow_lt_pow_left₀ hle ?_ ?_
      positivity
      linarith
    rw [aux] at absle
    linarith
    linarith
  obtain ⟨a, ha⟩ := (l_norm_eq_one_iff z).mp eq3
  obtain ⟨b, hb⟩ := (l_norm_eq_one_iff (z - 1)).mp eq4
  rw [Complex.exp_mul_I] at ha hb
  rw [←ha] at hb
  have aux1 : cos ↑b - cos ↑a  + 1 + (sin ↑b - sin ↑a) * I = 0 := by 
    calc 
      _ = (cos ↑b + sin ↑b * I ) - (cos ↑a + sin ↑a * I - 1) := by 
        ring
      _ = _ := by 
        rw [hb]
        ring
  norm_cast at aux1
  have eq5 : Real.sin b - Real.sin a = 0 := by
    have aux2 : (↑(Real.cos b - Real.cos a + 1) + ↑(Real.sin b - Real.sin a) * I).im = (Real.sin b - Real.sin a) := by 
        simp
        norm_cast
    norm_cast
    rw [aux1] at aux2
    simp at aux2
    exact Eq.symm aux2
  have eq6 : Real.sin b = Real.sin a:= by
    linarith
  have eq7 : Real.cos b - Real.cos a + 1= 0 := by
    have aux2 : (↑(Real.cos b - Real.cos a + 1) + ↑(Real.sin b - Real.sin a) * I).re =  (Real.cos b - Real.cos a + 1) := by
      simp
      norm_cast
    rw [aux1] at aux2
    simp at aux2
    exact Eq.symm aux2
  have eq8 : Real.cos b = Real.cos a - 1 := by
    linarith
  -- by Real.sin b = Real.sin a ∧ Real.cos b = Real.cos a - 1 
  have eq9 : Real.cos b ^ 2 = Real.cos a ^ 2 := by 
    rw [Real.cos_sq', Real.cos_sq']
    rw [eq6]
  rw [eq8] at eq9
  ring_nf at eq9
  have eq10 : Real.cos a = 1/ 2 := by 
    linarith
  have eq11 : Real.sin a = √3 / 2 ∨ Real.sin a = - (√3 / 2) := by
    have aux2 : Real.sin a ^ 2 = 3/4 := by
      rw [Real.sin_sq]
      rw [eq10]
      norm_num
    have aux3 : 3 / 4 =  (√3 / 2) ^ 2 := by
      rw [div_pow]
      simp
      norm_num
    rw [aux3] at aux2
    apply eq_or_eq_neg_of_sq_eq_sq
    exact aux2
  have eq1 : cos (a : ℂ) = Real.cos a := by 
    simp
  rw [eq10] at eq1
  obtain heq | heq := eq11
  have eq2 : sin (a : ℂ) = Real.sin a := by 
    simp 
  rw [heq] at eq2
  left
  rw [←ha, eq1, eq2]
  simp
  -- second case
  right
  have eq2 : sin (a : ℂ) = Real.sin a := by 
    simp 
  rw [heq] at eq2
  rw [←ha, eq1, eq2]
  simp
  ring