import Mathlib

theorem algebra_298203 {a b c : ℝ} (ha : ∀ x : ℤ, ∃ n : ℤ, a * x ^ 2 + b * x + c = n) :
    ∃ m n p : ℤ, 2 * a = m ∧ a - b = n ∧ c = p := by

  have h1 := ha 0
  rcases h1 with ⟨p, hp⟩
  have hp' : c = (p : ℝ) := by 
    norm_num at hp ⊢
    linarith

  have h2 := ha 1
  rcases h2 with ⟨q, hq⟩
  have eq1 : a + b + c = (q : ℝ) := by
    norm_num at hq ⊢
    linarith

  have h3 := ha (-1)
  rcases h3 with ⟨r, hr⟩
  have eq2 : a - b + c = (r : ℝ) := by
    norm_num at hr ⊢
    linarith
  
  use (q + r - 2 * p)
  use (r - p)
  use p
  
  constructor
  · -- Show that 2 * a = m
    have eq4 : 2 * a = (q + r - 2 * (p : ℝ) : ℝ) := by
      linarith [eq1, eq2, hp']
    norm_num at eq4 ⊢
    linarith
  
  constructor
  · -- Show that a - b = n
    have eq3 : a - b = (r - (p : ℝ) : ℝ) := by 
      linarith [eq2, hp']
    norm_num at eq3 ⊢
    linarith
  
  · -- Show that c = p
    norm_num at hp' ⊢
    linarith [hp']