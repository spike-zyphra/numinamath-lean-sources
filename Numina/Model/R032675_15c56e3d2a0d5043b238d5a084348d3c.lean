import Mathlib

theorem algebra_15779 (f : ℝ → ℝ)
    (h₀ : f 0 = 0)
    (h₁ : ∀ x y, 0 ≤ x → x < y → y ≤ 1 → f x ≤ f y)
    (h₂ : ∀ x, 0 ≤ x → x ≤ 1 → f (1 - x) = 1 - f x)
    (h₃ : ∀ x, 0 ≤ x → x ≤ 1 → f (x / 3) = (f x) / 2) :
    f (2 / 7) = 3 / 8 := by
  have h4 : f 1 = 1 := by
    have h5 : f (1 - 0) = 1 - f 0 := h₂ 0 (by norm_num) (by norm_num)
    rw [show 1 - (0 : ℝ) = 1 by norm_num] at h5
    rw [h₀] at h5
    linarith
  -- Determine f(1/3)
  have h6 : f (1/3) = 1/2 := by
    have h7 : f (1/3) = (f 1)/2 := by
      specialize h₃ 1 (by norm_num) (by norm_num)
      norm_num at h₃ ⊢
      linarith
    rw [h4] at h7
    linarith
  -- Determine f(2/3)
  have h10 : f (2/3) = 1/2 := by
    have h7 : f (1 - 1/3) = 1 - f (1/3) := by 
      apply h₂ 
      all_goals norm_num
    have h8 : (1 : ℝ) - 1/3 = 2/3 := by norm_num
    rw [h8] at h7 
    rw [h6] at h7 
    linarith
  -- Now we compute f(3/7), using that $1/3 \le 3/7 \le 2/3$ and f(1/3) = f(2/3) =1/2.
  -- Since f is increasing, $f(1/3) \le f(3/7) \le f(2/3)$, thus $1/2 \le f(3/7) \le1/2$, so $f(3/7)=1/2$.
  have h8 : f (3/7) = 1/2 := by
    have h9 : f (1/3) ≤ f (3/7) := by 
      apply h₁ 
      all_goals norm_num
    have h10' : f (3/7) ≤ f (2/3) := by 
      apply h₁ 
      all_goals norm_num 
    have h11 : f (1/3) = 1/2 := h6 
    have h12 : f (2/3) = 1/2 := h10 
    rw [h11] at h9 
    rw [h12] at h10' 
    linarith
  -- From h₃ with x=3/7, we have f(1/7)=f(3/7)/2=1/4.
  have h13 : f (1/7) = 1/4 := by
    have h14 : f (1/7) = (f (3/7)) / 2 := by 
      specialize h₃ (3/7) (by norm_num) (by norm_num) 
      have h15 : (3/7 : ℝ) / 3 = (1/7 : ℝ) := by norm_num 
      rw [h15] at h₃ 
      linarith 
    rw [h8] at h14 
    linarith 
  -- From h₂ with x=6/7, we have f(1/7)=1-f(6/7).
  -- So $f(6/7)=1-f(1/7)=1-1/4=3/4$.
  have h14 : f (6/7) = 3/4 := by
    have h15 : f (1 - (6/7 : ℝ)) = 1 - f (6/7) := h₂ (6/7) (by norm_num) (by norm_num)
    have h16 : 1 - (6/7 : ℝ) = 1/7 := by norm_num 
    rw [h16] at h15 
    linarith [h13] 
  -- From h₃ with x=6/7, we get f(2/7)=f(6/7)/2.
  -- Substituting $f(6/7)=3/4$, we get $f(2/7)=3/8$.
  have h15 : f (2/7) = (f (6/7)) / 2 := by
    specialize h₃ (6/7) (by norm_num) (by norm_num) 
    have h16 : (6/7 : ℝ) / 3 = (2/7 : ℝ) := by norm_num 
    rw [h16] at h₃ 
    linarith 
  rw [h14] at h15 
  linarith