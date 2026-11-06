import Mathlib

theorem algebra_304158 {a b c : ℝ} (ha : ∀ x : ℤ, ∃ n : ℤ, a * x ^ 2 + b * x + c = n) :
    ∃ m n p : ℤ, 2 * a = m ∧ a + b = n ∧ c = p := by 
  have h1 := ha 0
  rcases h1 with ⟨p, hp⟩
  have h2 := ha 1
  rcases h2 with ⟨q, hq⟩
  have h3 := ha (-1)
  rcases h3 with ⟨r, hr⟩
  have h4 := ha 2
  rcases h4 with ⟨s, hs⟩
  have h5 := ha (-2)
  rcases h5 with ⟨t, ht⟩
  have eq1 : c = (p : ℝ) := by 
    norm_num at hp
    linarith
  have eq2 : a + b = (q : ℝ) - (p : ℝ) := by 
    norm_num at hq
    linarith
  have eq3 : a - b = (r : ℝ) - (p : ℝ) := by
    norm_num at hr
    linarith
  have eq4 : 2 * a = (q + r - 2 * (p : ℝ)) := by
    linarith
  refine' ⟨q + r - 2 * p, q - p, p, by
    constructor
    · -- Show 2a = q + r - 2p
      have eq5 : 2 * a = (q + r - 2 * (p : ℝ)) := by
        linarith
      norm_num at eq5 ⊢
      <;> linarith
    constructor
    · -- Show a + b = q - p
      have eq6 : a + b = (q - (p : ℝ)) := by 
        linarith
      norm_num at eq6 ⊢
      <;> linarith
    · -- Show c = p
      have eq7 : c = (p : ℝ) := eq1
      norm_num at eq7 ⊢
      <;> linarith
  ⟩