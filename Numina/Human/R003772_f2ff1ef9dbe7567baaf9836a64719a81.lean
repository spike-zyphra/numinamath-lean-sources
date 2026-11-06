import Mathlib

theorem algebra_211931
  (f g h : ℝ → ℝ)
  (hf_pos : ∀ x, 0 < f x ↔ -2 < x ∧ x < 3)
  (hf_neg : ∀ x, f x < 0 ↔ x < -2 ∨ 3 < x)
  (hg_pos : ∀ x, 0 < g x ↔ x < 0 ∨ 5 < x)
  (hg_neg : ∀ x, g x < 0 ↔ 0 < x ∧ x < 5)
  (hh_pos : ∀ x, 0 < h x ↔ x > 1)
  (hh_neg : ∀ x, h x < 0 ↔ x < 1) :
  {x | (f x) * (g x) / (h x) > 0}
  = {x | x < -2 ∨ (0 < x ∧ x < 1) ∨ (3 < x ∧ x < 5)}  := by
  ext x
  simp
  constructor
  . intro hx

    rw [div_pos_iff] at hx
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    . rw [mul_pos_iff] at hx1
      rcases hx1 with ⟨hx1, hx3⟩ | ⟨hx1, hx3⟩
      . rw [hf_pos x] at hx1
        rw [hg_pos x] at hx3
        rw [hh_pos x] at hx2
        rcases hx3 with hx3 | hx3
        . linarith
        . linarith

      . rw [hf_neg x] at hx1
        rw [hg_neg x] at hx3
        rw [hh_pos x] at hx2
        rcases hx1 with hx1 | hx1
        . linarith
        . right; right
          constructor
          . linarith
          . linarith

    . rw [mul_neg_iff] at hx1
      rcases hx1 with ⟨hx1, hx3⟩ | ⟨hx1, hx3⟩
      . rw [hf_pos x] at hx1
        rw [hg_neg x] at hx3
        rw [hh_neg x] at hx2
        right; left
        constructor
        . linarith
        . linarith
      . rw [hf_neg x] at hx1
        rw [hg_pos x] at hx3
        rw [hh_neg x] at hx2
        rcases hx3 with hx3 | hx3
        . rcases hx1 with hx1 | hx1
          . left; exact hx1
          . linarith
        . linarith

  . intro hx

    rcases hx with hx | ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    . have h1 : f x < 0 := by
        rw [hf_neg x]
        left
        exact hx
      have h2 : 0 < g x := by
        rw [hg_pos x]
        left
        linarith
      have h3 : h x < 0 := by
        rw [hh_neg x]
        linarith

      have h4: f x * g x < 0 := by
        nlinarith

      exact div_pos_of_neg_of_neg h4 h3

    . have h1 : 0 < f x := by
        rw [hf_pos x]
        constructor
        . linarith
        . linarith
      have h2 : g x < 0 := by
        rw [hg_neg x]
        constructor
        . linarith
        . linarith
      have h3 : h x < 0 := by
        rw [hh_neg x]
        linarith

      have h4: f x * g x < 0 := by
        nlinarith

      exact div_pos_of_neg_of_neg h4 h3
    . have h1 : f x < 0 := by
        rw [hf_neg x]
        right
        exact hx1
      have h2 : g x < 0 := by
        rw [hg_neg x]
        constructor
        . linarith
        . linarith
      have h3 : 0 < h x := by
        rw [hh_pos x]
        linarith

      have h4: f x * g x > 0 := by
        nlinarith

      positivity
