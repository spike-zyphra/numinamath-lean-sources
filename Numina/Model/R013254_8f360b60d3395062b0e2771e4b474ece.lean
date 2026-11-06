import Mathlib

theorem algebra_290107 {a b c : ℝ} (ha : a ≠ 0) (hroots : ∃ x y, x ≠ y ∧ a*x^2+b*x+c=0 ∧ a*y^2+b*y+c=0 ∧ x=4*y) :
    16*b^2/(a*c) = 100 := by
  rcases hroots with ⟨x, y, hneq, hx, hy, hx4y⟩
  have h1 : a * x ^ 2 + b * x + c - (a * y ^ 2 + b * y + c) = 0 := by linarith [hx, hy]
  have h2 : a * (x ^ 2 - y ^ 2) + b * (x - y) = 0 := by
    nlinarith
  have h3 : (x - y) * (a * (x + y) + b) = 0 := by
    ring_nf at h2 ⊢
    linarith
  cases (mul_eq_zero.mp h3) with
  | inl h4 =>
    exfalso
    exact hneq (by linarith)
  | inr h3 =>
    have eq1 : 5 * a * y + b = 0 := by
      rw [show x = 4 * y by linarith [hx4y]] at h3
      linarith
    have eq2 : a * (4 * y) ^ 2 + b * (4 * y) + c = 0 := by
      rw [show x = 4 * y by linarith [hx4y] ] at hx
      linarith
    have eq3 : a * y ^ 2 + b * y + c = 0 := by
      linarith [hy]
    have eq4 : b = -5 * a * y := by
      linarith [eq1]
    have eq5 : c = 4 * a * y ^ 2 := by
      rw [eq4] at eq3
      nlinarith
    have h2' : 16 * b ^ 2 = 100 * a * c := by 
      rw [eq4, eq5]
      nlinarith
    have hcne0 : c ≠ 0 := by
      by_contra h
      have hb0 : b = 0 := by
        have h2'' : 16 * b ^ 2 = 0 := by
          rw [h] at h2'
          nlinarith [h2']
        have hb0 : b ^ 2 = 0 := by nlinarith
        have : b = 0 := by nlinarith
        assumption
      have hy0 : y = 0 := by 
        rw [hb0] at eq4
        have : -5 * a * y = 0 := by linarith [eq4]
        have hne : a ≠ 0 := by exact ha
        have : y = 0 := by 
          apply (mul_right_inj' hne).mp
          linarith
        assumption
      have hx0 : x = 0 := by
        linarith [hx4y, hy0]
      have hfalse : x ≠ y := hneq
      have : x = y := by
        linarith [hx0, hy0]
      contradiction
    have hfrac : 16 * b ^ 2 / (a * c) = 100 := by
      have denominne : a * c ≠ 0 := by
        apply mul_ne_zero
        exact ha
        exact hcne0
      field_simp [denominne]
      linarith [h2']
    exact hfrac