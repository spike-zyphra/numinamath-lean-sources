import Mathlib

theorem algebra_301531 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : (b + c - a) / a = (c + a - b) / b) (h2 : (c + a - b) / b = (a + b - c) / c) :
    ((a + b) * (b + c) * (c + a)) / (a * b * c) = -1 ∨ ((a + b) * (b + c) * (c + a)) / (a * b * c) = 8 := by
  have h1' : (b + c - a) * b = (c + a - b) * a := by
    have hne1 : a ≠ 0 := ha
    have hne2 : b ≠ 0 := hb
    field_simp [hne1, hne2] at h1 ⊢
    nlinarith

  have h2' : (c + a - b) * c = (a + b - c) * b := by
    have hne1 : b ≠ 0 := hb
    have hne2 : c ≠ 0 := hc
    field_simp [hne1, hne2] at h2 ⊢
    nlinarith

  have eq1 : (b - a) * (a + b + c) = 0 := by 
    linarith [h1']

  have eq2 : (c - b) * (a + b + c) = 0 := by 
    linarith [h2']

  by_cases h : a + b + c = 0
  · -- Case $a + b + c = 0$, compute $\frac{(a + b)(b + c)(c + a)}{abc} = -1$
    have hab1 : a + b = -c := by linarith 
    have hab2 : b + c = -a := by linarith 
    have hab3 : c + a = -b := by linarith 
    have h3 : (a + b) * (b + c) * (c + a) = - (a * b * c) := by 
      rw [hab1, hab2, hab3]
      ring
    have h4 : ((a + b) * (b + c) * (c + a)) / (a * b * c) = -1 := by
      rw [h3]
      have h5 : a * b * c ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        exact ha
        exact hb
        exact hc
      field_simp [h5]
      <;> ring
    left 
    linarith [h4]
  · -- Case $a + b + c ≠ 0$, compute $\frac{(a + b)(b + c)(c + a)}{abc} = 8$
    have hne1 : b - a = 0 := by 
      have hw : a + b + c ≠ 0 := h
      have : b - a = 0 := by 
        apply_fun (fun x => x / (a + b + c)) at eq1
        field_simp [hw] at eq1 ⊢
        <;> linarith 
      assumption 
    have hne2 : c - b = 0 := by 
      have hw : a + b + c ≠ 0 := h
      have : c - b = 0 := by 
        apply_fun (fun x => x / (a + b + c)) at eq2
        field_simp [hw] at eq2 ⊢
        <;> linarith 
      assumption 
    have hab1 : a = b := by linarith 
    have hab2 : b = c := by linarith 
    have hab3 : a = c := by linarith [hab1, hab2] 
    have h3 : (a + b) * (b + c) * (c + a) = 8 * (a * b * c) := by 
      rw [show b = a by linarith, show c = a by linarith] 
      ring 
    have h4 : ((a + b) * (b + c) * (c + a)) / (a * b * c) = 8 := by 
      have h5 : a * b * c ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        exact ha
        exact hb
        exact hc
      rw [h3] 
      field_simp [h5] 
      <;> ring 
    right 
    linarith [h4]