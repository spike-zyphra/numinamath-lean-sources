import Mathlib

theorem Number_theory_611037  (s : ℕ → ℝ) (hs0 : s 0 = 1) (hs1 : s 1 = 1) (h2n: ∀ n, s (2*n) = (s n)) (h4np1: ∀ n, s (4*n+1) = s (2*n+1) ) (h4nm1: ∀ n, s (4*n-1) = s (2*n-1) + (s (2*n-1))^2/ (s (n-1)) ) : s 1000 = 720 := by

  have h3 : s 3 = 2 := by
    specialize h4nm1 1
    norm_num [hs1,hs0] at h4nm1 ⊢
    <;> linarith

  have h7 : s 7 = 6 := by 
    specialize h4nm1 2
    norm_num [hs1,h3] at h4nm1 ⊢
    <;> nlinarith

  have h15 : s 15 = 24 := by 
    specialize h4nm1 4
    norm_num [hs1,h7,h3] at h4nm1 ⊢
    <;> nlinarith

  have h31 : s 31 = 120 := by
    specialize h4nm1 8
    norm_num [hs1,h7,h15] at h4nm1 ⊢
    <;> nlinarith

  have h63 : s 63 = 720 := by 
    specialize h4nm1 16
    norm_num [hs1,h31, h15] at h4nm1 ⊢
    <;> nlinarith

  have h125 : s 125 = 720 := by
    specialize h4np1 31
    norm_num [h63] at h4np1 ⊢
    <;> linarith

  have h250 : s 250 = 720 := by
    specialize h2n 125
    norm_num [h125] at h2n ⊢
    <;> linarith

  have h500 : s 500 = 720 := by 
    specialize h2n 250
    norm_num [h250] at h2n ⊢
    <;> linarith

  have h1000 : s 1000 = 720 := by 
    specialize h2n 500
    norm_num [h500] at h2n ⊢
    <;> linarith
  
  exact h1000