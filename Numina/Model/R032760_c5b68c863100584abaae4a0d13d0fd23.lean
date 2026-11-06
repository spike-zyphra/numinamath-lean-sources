import Mathlib

/- Let $k$, $l$, $m$ be real numbers, with $m \ne 0$. In the Cartesian coordinate system, the graph of the function $y = f(x) = k + \frac{m}{x-l}$ is the curve $C_1$. The graph of another function $y = g(x)$ is the curve $C_2$, and it satisfies that $C_2$ is symmetric to $C_1$ with respect to the line $y = x$. If the points $(1,4)$, $(2,3)$, $(2,4)$ are on either curve $C_1$ or $C_2$, then the value of $f(k+l+m)$ is ___          ___. -/
theorem algebra_13126 (k l m : ℝ) (hm : m ≠ 0) (f g : ℝ → ℝ)
    (hf : f = fun x => k + m / (x - l)) (hg : g = fun x => l + m / (x - k))
    (h₁ : f 1 = 4) (h₂ : f 2 = 3) (h₃ : g 2 = 4) :
    f (k + l + m) = 1 ∨ f (k + l + m) = -4 / 5 := by
  have eq1 : k + m / (1 - l) = 4 := by
    rw [hf] at h₁
    norm_num at h₁ ⊢
    exact h₁
  have eq2 : k + m / (2 - l) = 3 := by
    rw [hf] at h₂
    norm_num at h₂ ⊢
    exact h₂
  have eq3 : l + m / (2 - k) = 4 := by
    rw [hg] at h₃
    norm_num at h₃ ⊢
    exact h₃
  by_cases h4 : 1 - l = 0
  · -- Assume 1 - l = 0, so l = 1
    have h5 : l = 1 := by linarith 
    have eq1' : k = 4 := by 
      rw [h5] at eq1
      norm_num [h5] at eq1 ⊢
      linarith 
    rw [show l = 1 by linarith [h5]] at eq2 eq3
    have eq2' : k + m / (2 - 1) = 3 := eq2
    have eq3' : (1 : ℝ) + m / (2 - k) = 4 := eq3
    rw [show k = 4 by linarith [eq1']] at eq3' 
    norm_num at eq3' eq2' ⊢ 
    all_goals nlinarith 
  · -- Assume 1 - l ≠ 0 
    have eq1' : (k) = 4 - m / (1 - l) := by 
      have h1 : k + m / (1 - l) = 4 := eq1 
      have h11 : 1 - l ≠ 0 := by
        by_contra h11
        have h4' : 1 - l = 0 := by linarith 
        contradiction
      field_simp [h11] at h1 ⊢ 
      linarith 
    by_cases h5 : 2 - l = 0 
    · -- Assume 2 - l = 0, so l = 2
      have hl2 : l = 2 := by linarith 
      have eq2' : k = 3 := by 
        rw [hl2] at eq2
        norm_num [hl2] at eq2 ⊢
        linarith 
      have eq4 : k + m / (1 - l) = 4 := eq1 
      rw [hl2] at eq4 
      norm_num [hl2] at eq4 ⊢ 
      have eq6 : m = -1 := by 
        linarith 
      have eq3' : l + m / (2 - k) = 4 := eq3 
      rw [hl2] at eq3' 
      rw [eq2'] at eq3' 
      norm_num at eq3' ⊢ 
      all_goals nlinarith 
    · -- Assume 2 - l ≠ 0 
      have eq2' : (k) = 3 - m / (2 - l) := by 
        have h11 : k + m / (2 - l) = 3 := eq2 
        have h12 : 2 - l ≠ 0 := by
          by_contra h12 
          have h5' : 2 - l = 0 := by linarith 
          contradiction 
        field_simp [h12] at h11 ⊢ 
        linarith 
      have eq6 : (4 - m / (1 - l) ) = (3 - m / (2 - l) ) := by 
        linarith [eq1', eq2'] 
      have hne1 : 1 - l ≠ 0 := by 
        exact h4 
      have hne2 : 2 - l ≠ 0 := by 
        exact h5 
      have eqm : m = (1 - l) * (2 - l) := by 
        field_simp [hne1, hne2] at eq6 ⊢ 
        nlinarith 
      have eq7 : 2 - k = - l := by 
        have eq11 : k = 4 - m / (1 - l) := eq1'
        have eq12 : k = 3 - m / (2 - l) := eq2'
        field_simp [hne1, hne2] at eq11 eq12 
        nlinarith [sq_pos_of_ne_zero hm, sq_nonneg (1 - l), sq_nonneg (2 - l)]
      have eq3' : l + m / (2 - k) = 4 := eq3 
      have h7 : 2 - k = - l := eq7 
      rw [show 2 - k = - l by linarith [eq7] ] at eq3' 
      by_cases h6 : l = 0 
      · -- Assume l = 0 
        have eq8 : l = 0 := by linarith 
        rw [eq8] at eq3' eqm 
        norm_num [eq8] at eq3' eqm 
        all_goals 
          try { tauto }
      · -- Assume l ≠ 0 
        have h6' : l ≠ 0 := by 
          exact h6 
        have eq8 : m = (1 - l) * (2 - l) := eqm 
        rw [eq8] at eq3' 
        field_simp [h6'] at eq3' 
        have hl : l = -2 := by 
          nlinarith [sq_pos_of_ne_zero hm, sq_nonneg (l + 2), sq_nonneg (1 - l), sq_nonneg (2 - l)]
        have hm' : m = 12 := by 
          rw [hl] at eq8 
          nlinarith 
        have hk : k = 0 := by 
          linarith [eq7, hl] 
        have h5 : f (k + l + m) = 1 := by 
          rw [hf]
          simp only [hk, hl, hm']
          norm_num 
        left 
        exact h5