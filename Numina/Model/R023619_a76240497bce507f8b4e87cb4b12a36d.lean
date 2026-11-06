import Mathlib

theorem algebra_303579 {a b : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^2 + a * x + b)
    (h0 : f (f 0) = 0) (h1 : f (f 1) = 0) (h2 : f 0 ≠ f 1) : f 2 = 3 := by

  have h3 : f 0 = b := by 
    rw [hf]
    norm_num 
    <;> ring

  have h4 : f 1 = 1 + a + b := by 
    rw [hf]
    norm_num 
    <;> ring

  have h5 : f (f 0) = (b ^ 2 + a * b + b) := by
    rw [h3]
    rw [hf]
    all_goals
      simp 
      <;> ring

  have h6 : f (f 1) = (1 + a + b) ^ 2 + a * (1 + a + b) + b := by
    rw [h4]
    rw [hf]
    all_goals
      simp
      <;> ring

  rw [h5] at h0
  rw [h6] at h1

  have eq1 : b * (b + a + 1) = 0 := by
    nlinarith

  have eq5 : b ≠ 1 + a + b := by
    intro h
    have : f 0 = f 1 := by
      rw [h3, h4]
      nlinarith [h]
    tauto

  cases' (mul_eq_zero.mp eq1) with h7 h8
  · -- Case b = 0
    have hb0 : b = 0 := by
      linarith
    rw [hb0] at h0 h1
    have ha2 : 2 * a ^ 2 + 3 * a + 1 = 0 := by
      nlinarith
    have eq2 : (a + 1 / 2) * (a + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq2) with ha3 ha4
    · -- Case a = -1/2 
      have ha4' : a = -1 / 2 := by linarith
      have h7 : f 2 = 3 := by 
        rw [hf]
        norm_num [ha4', hb0]
        <;> linarith
      linarith [h7]
    · -- Case a = -1
      have ha5' : a = -1 := by linarith
      exfalso
      have h2' : f 0 = f 1 := by
        rw [h3, h4]
        nlinarith [hb0, ha5']
      tauto
  · -- Case b + a + 1 = 0
    have eq3 : b = -a - 1 := by 
      linarith
    have eq4a : f 0 = -a - 1 := by 
      rw [h3]
      nlinarith [eq3]
    have eq4b : f 1 = (0 : ℝ) := by 
      rw [h4]
      nlinarith [eq3]
    have eq5b : f 0 ≠ f 1 := h2
    rw [eq4a, eq4b] at eq5b
    exfalso 
    have eq3' : b = (0 : ℝ) := by 
      nlinarith [sq_nonneg (1 + a + b), sq_nonneg (a * b), sq_nonneg ((1 + a) * b)]
    have eq3a : a = -1 := by 
      nlinarith [eq3, eq3']
    have eq4a : f 0 = f 1 := by 
      rw [h3, h4]
      nlinarith [eq3', eq3a]
    tauto