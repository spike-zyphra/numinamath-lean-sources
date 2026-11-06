import Mathlib

theorem algebra_199955 {f : ℝ → ℝ} (hf : ∃ p : Polynomial ℝ, p.degree = 7 ∧ ∀ x : ℝ, f x = p.eval x)
    (h : f (-4) = 0 ∧ f (-3) = 1 ∧ f (-2) = 0 ∧ f (-1) = -1 ∧ f 0 = 0 ∧ f 1 = 1 ∧ f 2 = 0 ∧ f 3 = -1 ∧ f 4 = 0) :
    f = fun x => -1/630 * x^7 + 1/18 * x^5 - 26/45 * x^3 + 32/21 * x := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases hf with ⟨p, hp1, hp2⟩
  have eq1 : f (-4) = p.eval (-4) := by
    apply hp2
  have eq2 : f (-3) = p.eval (-3) := by
    apply hp2
  have eq3 : f (-2) = p.eval (-2) := by 
    apply hp2
  have eq4 : f (-1) = p.eval (-1) := by 
    apply hp2
  have eq5 : f 0 = p.eval (0) := by 
    apply hp2
  have eq6 : f 1 = p.eval 1 := by 
    apply hp2
  have eq7 : f 2 = p.eval 2 := by 
    apply hp2
  have eq8 : f 3 = p.eval 3 := by 
    apply hp2
  have eq9 : f 4 = p.eval 4 := by 
    apply hp2
  simp [eq1] at h1
  simp [eq2] at h2
  simp [eq3] at h3
  simp [eq4] at h4
  simp [eq5] at h5
  simp [eq6] at h6
  simp [eq7] at h7
  simp [eq8] at h8
  simp [eq9] at h9
  have h7 : p.natDegree = 7 := by 
    rw [Polynomial.natDegree_eq_of_degree_eq_some hp1]
    all_goals simp
  have eq10 : p.eval (-4) = 0 := by linarith
  have eq11 : p.eval (-3) = 1 := by linarith
  have eq12 : p.eval (-2) = 0 := by linarith
  have eq13 : p.eval (-1) = -1 := by linarith
  have eq14 : p.eval (0) = 0 := by linarith
  have eq15 : p.eval 1 = 1 := by linarith
  have eq16 : p.eval 2 = 0 := by linarith
  have eq17 : p.eval 3 = -1 := by linarith
  have eq18 : p.eval 4 = 0 := by linarith
  have eq19 : p.eval (-4) = p.coeff 7 * (-4) ^ 7 + p.coeff 6 * (-4) ^ 6 + p.coeff 5 * (-4) ^ 5 + p.coeff 4 * (-4) ^ 4 + p.coeff 3 * (-4) ^ 3 + p.coeff 2 * (-4) ^ 2 + p.coeff 1 * (-4) + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  have eq20 : p.eval (-3) = p.coeff 7 * (-3) ^ 7 + p.coeff 6 * (-3) ^ 6 + p.coeff 5 * (-3) ^ 5 + p.coeff 4 * (-3) ^ 4 + p.coeff 3 * (-3) ^ 3 + p.coeff 2 * (-3) ^ 2 + p.coeff 1 * (-3) + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  have eq21 : p.eval (-2) = p.coeff 7 * (-2) ^ 7 + p.coeff 6 * (-2) ^ 6 + p.coeff 5 * (-2) ^ 5 + p.coeff 4 * (-2) ^ 4 + p.coeff 3 * (-2) ^ 3 + p.coeff 2 * (-2) ^ 2 + p.coeff 1 * (-2) + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  have eq22 : p.eval (-1) = p.coeff 7 * (-1) ^ 7 + p.coeff 6 * (-1) ^ 6 + p.coeff 5 * (-1) ^ 5 + p.coeff 4 * (-1) ^ 4 + p.coeff 3 * (-1) ^ 3 + p.coeff 2 * (-1) ^ 2 + p.coeff 1 * (-1) + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  have eq23 : p.eval (0) = p.coeff 7 * (0 : ℝ) ^ 7 + p.coeff 6 * (0 : ℝ) ^ 6 + p.coeff 5 * (0 : ℝ) ^ 5 + p.coeff 4 * (0 : ℝ) ^ 4 + p.coeff 3 * (0 : ℝ) ^ 3 + p.coeff 2 * (0 : ℝ) ^ 2 + p.coeff 1 * (0 : ℝ) + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  have eq24 : p.eval 1 = p.coeff 7 * (1 : ℝ) ^ 7 + p.coeff 6 * (1 : ℝ) ^ 6 + p.coeff 5 * (1 : ℝ) ^ 5 + p.coeff 4 * (1 : ℝ) ^ 4 + p.coeff 3 * (1 : ℝ) ^ 3 + p.coeff 2 * (1 : ℝ) ^ 2 + p.coeff 1 * (1 : ℝ) + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  have eq25 : p.eval 2 = p.coeff 7 * (2 : ℝ) ^ 7 + p.coeff 6 * (2 : ℝ) ^ 6 + p.coeff 5 * (2 : ℝ) ^ 5 + p.coeff 4 * (2 : ℝ) ^ 4 + p.coeff 3 * (2 : ℝ) ^ 3 + p.coeff 2 * (2 : ℝ) ^ 2 + p.coeff 1 * (2 : ℝ) + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  have eq26 : p.eval 3 = p.coeff 7 * (3 : ℝ) ^ 7 + p.coeff 6 * (3 : ℝ) ^ 6 + p.coeff 5 * (3 : ℝ) ^ 5 + p.coeff 4 * (3 : ℝ) ^ 4 + p.coeff 3 * (3 : ℝ) ^ 3 + p.coeff 2 * (3 : ℝ) ^ 2 + p.coeff 1 * (3 : ℝ) + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  have eq27 : p.eval 4 = p.coeff 7 * (4 : ℝ) ^ 7 + p.coeff 6 * (4 : ℝ) ^ 6 + p.coeff 5 * (4 : ℝ) ^ 5 + p.coeff 4 * (4 : ℝ) ^ 4 + p.coeff 3 * (4 : ℝ) ^ 3 + p.coeff 2 * (4 : ℝ) ^ 2 + p.coeff 1 * (4 : ℝ) + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  have eq28 : p.coeff 7 = -1 / 630 := by 
    norm_num at eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18
    norm_num at eq19 eq20 eq21 eq22 eq23 eq24 eq25 eq26 eq27
    linarith
  have eq29 : p.coeff 6 = 0 := by 
    norm_num at eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18
    norm_num at eq19 eq20 eq21 eq22 eq23 eq24 eq25 eq26 eq27
    linarith
  have eq30 : p.coeff 5 = 1 / 18 := by 
    norm_num at eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18
    norm_num at eq19 eq20 eq21 eq22 eq23 eq24 eq25 eq26 eq27
    linarith
  have eq31 : p.coeff 4 = 0 := by 
    norm_num at eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18
    norm_num at eq19 eq20 eq21 eq22 eq23 eq24 eq25 eq26 eq27
    linarith
  have eq32 : p.coeff 3 = -26 / 45 := by 
    norm_num at eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18
    norm_num at eq19 eq20 eq21 eq22 eq23 eq24 eq25 eq26 eq27
    linarith
  have eq33 : p.coeff 2 = 0 := by 
    norm_num at eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18
    norm_num at eq19 eq20 eq21 eq22 eq23 eq24 eq25 eq26 eq27
    linarith
  have eq34 : p.coeff 1 = 32 / 21 := by 
    norm_num at eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18
    norm_num at eq19 eq20 eq21 eq22 eq23 eq24 eq25 eq26 eq27
    linarith
  have eq35 : p.coeff 0 = 0 := by 
    norm_num at eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18
    norm_num at eq19 eq20 eq21 eq22 eq23 eq24 eq25 eq26 eq27
    linarith
  funext x
  have hfx : f x = p.eval x := by
    apply hp2
  rw [hfx]
  have eq36 : p.eval x = p.coeff 7 * x ^ 7 + p.coeff 6 * x ^ 6 + p.coeff 5 * x ^ 5 + p.coeff 4 * x ^ 4 + p.coeff 3 * x ^ 3 + p.coeff 2 * x ^ 2 + p.coeff 1 * x + p.coeff 0 := by 
    simp [Polynomial.eval_eq_sum_range, h7, Finset.sum_range_succ, mul_add, add_mul]
    <;> ring
  rw [eq36]
  rw [eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35]
  ring_nf