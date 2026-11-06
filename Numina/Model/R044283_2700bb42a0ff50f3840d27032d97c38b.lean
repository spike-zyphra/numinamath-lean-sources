import Mathlib

theorem algebra_8278 {a b : ℝ} (f : ℝ → ℝ) (hf : f = fun x => (x^2 + 1) / (a * x + b))
    (hodd : ∀ x, f (-x) = -f x) (hf1 : f 1 = 2) (ht : t < 0)
    (h : ℝ → ℝ) (hh : h = fun x => x^2 + 1 / x^2 - 2 * t * f x)
    (h' : ∀ x1 x2 : ℝ, x1 ∈ Set.Icc (1 / 2) 1 → x2 ∈ Set.Icc (1 / 2) 1 →
      |h x1 - h x2| ≤ 15 / 4) :
    t ≥ -3 / 2 := by

  have h1 : a + b = 1 := by
    have eq1 : f 1 = 2 := hf1
    rw [hf] at eq1
    norm_num at eq1 
    by_cases h2 : a + b = 0
    · 
      rw [show a + b = (0 : ℝ) by linarith [h2]] at eq1
      norm_num at eq1 
    · 
      have h3 : a + b ≠ 0 := by 
        intro heq
        have h4 : a + b = 0 := by linarith [heq]
        tauto 
      have eq3 : (a + b) = 1 := by 
        field_simp [(show (a + b : ℝ) ≠ 0 by 
          tauto 
        )] at eq1 
        all_goals 
          linarith
      exact eq3

  have h2 : b = 0 := by
    have eq1 : f (-1) = -f 1 := hodd 1
    have eq2 : f (-1) = 2 / (-a + b) := by 
      rw [hf]
      norm_num 
    have eq3 : f 1 = 2 / (a + b) := by 
      rw [hf]
      norm_num 
    rw [eq2, eq3] at eq1 
    have eq4 : a + b = 1 := h1 
    rw [show a + b = 1 by linarith] at eq1 
    have eq7 : 2 / (-a + b) = -2 := by 
      norm_num at eq1 ⊢
      all_goals 
        linarith 
    have eq8 : -a + b ≠ 0 := by 
      by_contra h
      rw [show -a + b = (0 : ℝ) by linarith] at eq7 
      norm_num at eq7 
    have eq3 : -a + b = -1 := by 
      have eq4 : 2 / (-a + b) = -2 := eq7 
      have h3 : -a + b ≠ 0 := eq8 
      field_simp [(show (-a + b : ℝ) ≠ 0 by tauto)] at eq4 
      all_goals 
        nlinarith
    have eq9 : b = 0 := by 
      have h10 : a + b = 1 := h1 
      have h11 : -a + b = -1 := eq3 
      nlinarith
    exact eq9

  have h3 := h' (1 / 2 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)

  have eq3 : h (1 / 2 : ℝ) = (1 / 2 : ℝ)^2 + 1 / (1 / 2 : ℝ)^2 - 2 * t * f (1 / 2 : ℝ) := by
    rw [hh]

  have eq4 : h (1 : ℝ) = (1 : ℝ)^2 + 1 / (1 : ℝ)^2 - 2 * t * f (1 : ℝ) := by
    rw [hh]

  have eq5 : f (1 / 2 : ℝ) = 5 / 2 := by
    rw [hf]
    simp [show a = 1 by linarith [h1], show b = 0 by linarith [h2]]
    all_goals norm_num

  have eq6 : f (1 : ℝ) = 2 := by
    rw [hf]
    simp [show a = 1 by linarith [h1], show b = 0 by linarith [h2]]
    all_goals norm_num

  rw [eq3, eq4, eq5, eq6] at h3

  have eq7 : (1 / 2 : ℝ)^2 + 1 / (1 / 2 : ℝ)^2 - 2 * t * (5 / 2 : ℝ) = 17 / 4 - 5 * t := by
    norm_num
    all_goals ring

  have eq8 : (1 : ℝ)^2 + 1 / (1 : ℝ)^2 - 2 * t * (2 : ℝ) = 2 - 4 * t := by
    norm_num
    all_goals ring

  rw [eq7, eq8] at h3

  have eq9 : - (15 / 4 : ℝ) ≤ (17 / 4 - 5 * t : ℝ) - (2 - 4 * t : ℝ) := by
    linarith [abs_le.mp h3]

  have eq10 : (17 / 4 - 5 * t : ℝ) - (2 - 4 * t : ℝ) ≤ 15 / 4 := by
    linarith [abs_le.mp h3]

  have eq11 : (17 / 4 - 5 * t : ℝ) - (2 - 4 * t : ℝ) = 9 / 4 - t := by
    linarith

  rw [eq11] at eq9
  rw [eq11] at eq10

  all_goals
    linarith