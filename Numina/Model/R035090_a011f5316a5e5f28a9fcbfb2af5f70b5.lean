import Mathlib

theorem algebra_323724 (x : ℕ → ℤ)
    (hx1 : x 1 = 1)
    (hxn : ∀ k ≥ 2, x k = x (k - 1) + 1 - 4 * ((k - 1) / 4 - (k - 2) / 4)) :
    x 2010 = 2 := by
  have h2 : x 2 = 2 := by 
    norm_num [hx1, hxn]
    all_goals omega 
  have h3 : x 3 = 3 := by 
    norm_num [hx1, hxn, h2]
    all_goals omega 
  have h4 : x 4 = 4 := by 
    norm_num [hx1, hxn, h2, h3]
    all_goals omega 
  have h5 : x 5 = 1 := by 
    norm_num [hx1, hxn, h2, h3, h4]
    all_goals omega 
  have h6 : x 6 = 2 := by 
    norm_num [hx1, hxn, h2, h3, h4, h5]
    all_goals omega 
  have h7 : ∀ (n : ℕ), x (4 * n + 2) = 2 := by
    intro n 
    induction n with
    | zero =>
      norm_num [hx1, hxn, h2]
    | succ n ih =>
      have eq1 : x (4 * (n + 1 : ℕ) + 2) = x (4 * n + 6) := by
        simp [mul_add, add_assoc]
        <;> ring_nf <;> omega
      rw [eq1]
      have h8 : x (4 * n + 3) = 3 := by
        have h1 : x (4 * n + 3) = x (4 * n + 2) + 1 - 4 * (((4 * n + 3 - 1) / 4) - ((4 * n + 3 - 2) / 4)) := by 
          apply hxn 
          omega 
        rw [h1, ih]
        all_goals omega 
      have h9 : x (4 * n + 4) = 4 := by
        have h1 : x (4 * n + 4) = x (4 * n + 3) + 1 - 4 * (((4 * n + 4 - 1) / 4) - ((4 * n + 4 - 2) / 4)) := by 
          apply hxn 
          omega 
        rw [h1, h8]
        all_goals omega 
      have h10 : x (4 * n + 5) = 1 := by
        have h1 : x (4 * n + 5) = x (4 * n + 4) + 1 - 4 * (((4 * n + 5 - 1) / 4) - ((4 * n + 5 - 2) / 4)) := by 
          apply hxn 
          omega 
        rw [h1, h9]
        all_goals omega 
      have h11 : x (4 * n + 6) = 2 := by
        have h1 : x (4 * n + 6) = x (4 * n + 5) + 1 - 4 * (((4 * n + 6 - 1) / 4) - ((4 * n + 6 - 2) / 4)) := by 
          apply hxn 
          omega 
        rw [h1, h10]
        all_goals omega 
      linarith 
  specialize h7 502 
  norm_num at h7 ⊢
  all_goals omega 
  all_goals omega