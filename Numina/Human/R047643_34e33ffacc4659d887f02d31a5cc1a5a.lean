import Mathlib

/- 1. Given $\frac{a b}{a+b}=\frac{1}{15}, \frac{b c}{b+c}=\frac{1}{17}, \frac{c a}{c+a}=\frac{1}{16}$. Then the value of $\frac{a b c}{a b+b c+c a}$ is ( ).
(A) $\frac{1}{21}$
(B) $\frac{1}{22}$
(C) $\frac{1}{23}$
(D) $\frac{1}{24}$ -/
theorem algebra_306420 {a b c : ℝ} (h₀ : a * b / (a + b) = 1 / 15) (h₁ : b * c / (b + c) = 1 / 17)
    (h₂ : c * a / (c + a) = 1 / 16) :
    a * b * c / (a * b + b * c + c * a) = 1 / 24 := by
  -- first we prove that a ≠ 0, b ≠ 0, c ≠ 0
  have neq1 : a ≠ 0 := by 
    by_contra h'
    rw [h'] at h₀
    simp at h₀
  have neq2 : b ≠ 0 := by 
    by_contra h'
    rw [h'] at h₀
    simp at h₀
  have neq3 : c ≠ 0 := by 
    by_contra h'
    rw [h'] at h₁
    simp at h₁
  -- 1 / a + 1 / b = 15
  have eq_aux1 : 1 / a + 1 / b = 15 := by
    have aux : (a + b)/ (a * b) = 15 := by 
      have aux' : 15 = 1 / (1 / (15 : ℝ)) := by 
        norm_num
      rw [aux']
      rw [←h₀]
      field_simp
    rw [←aux]
    field_simp
    ring_nf
  -- 1 / b + 1 / c = 17
  have eq_aux2 : 1 / b + 1 / c = 17 := by
    have aux : (b + c)/ (b * c) = 17 := by 
      have aux' : 17 = 1 / (1 / (17 : ℝ)) := by 
        norm_num
      rw [aux']
      rw [←h₁]
      field_simp
    rw [←aux]
    field_simp
    ring_nf
  -- 1 / c + 1 / a = 16
  have eq_aux3 : 1 / c + 1 / a = 16 := by
    have aux : (c + a)/ (c * a) = 16 := by
      have aux' : 16 = 1 / (1 / (16 : ℝ)) := by
        norm_num
      rw [aux']
      rw [←h₂]
      field_simp
    rw [←aux]
    field_simp
    ring_nf
  -- add all three equation to get 2 * (1/a + 1/b + 1/c) = 48
  have eq_add : 2 * (1/a + 1/b + 1/c) = 48 := by nlinarith
  have eq_add' : (1/a + 1/b + 1/c) = 24 := by linarith
  rw [←eq_add']
  field_simp
  ring