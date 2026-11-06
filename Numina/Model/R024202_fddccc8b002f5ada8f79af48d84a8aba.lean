import Mathlib

theorem algebra_4317 {f : ℝ → ℝ} (h : ∀ a b, f (a + b) = f a + f b)
    (h' : f 2008 = 3012) : f 2009 = 3012 * 2009 / 2008 := by

  have h1 : f 2008 = 2008 * f 1 := by
    have eq1 : ∀ (n : ℕ), f ((n : ℝ) * 1) = (n : ℝ) * f 1 := by
      intro n 
      induction n with
      | zero =>
        simp 
        <;> norm_num [h]
        all_goals 
          have h1 : f 0 = 0 := by 
            specialize h 0 0 
            simp at h ⊢ 
            <;> linarith 
          simp [h1]
          <;> norm_num [h]
          <;> linarith 
      | succ n ih =>
        have eq2 : ((n + 1 : ℕ) : ℝ) * 1 = (n : ℝ) * 1 + 1 := by
          simp at *
          <;> ring_nf <;> norm_num 
          all_goals tauto
        rw [eq2]
        rw [h]
        simp at ih ⊢
        <;> ring_nf at ih ⊢ <;> norm_num [h] at ih ⊢ 
        all_goals nlinarith
    specialize eq1 2008
    norm_num at eq1 ⊢
    all_goals nlinarith 
  have h2 : f 1 = 3012 / 2008 := by
    have eq1 : 2008 * f 1 = 3012 := by 
      linarith [h', h1]
    have eq2 : f 1 = 3012 / 2008 := by
      field_simp at *
      <;> nlinarith
    exact eq2
  have h3 : f 2009 = f 2008 + f 1 := by
    specialize h 2008 1
    rw [show (2008 : ℝ) + (1 : ℝ) = (2009 : ℝ) by norm_num] at h
    linarith
  rw [h'] at h3
  rw [h2] at h3
  field_simp at h3 ⊢
  <;> nlinarith