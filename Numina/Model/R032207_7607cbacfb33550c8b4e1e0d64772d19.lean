import Mathlib

theorem number_theory_210361 (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ¬(IsSquare (p^2 + q) ∧ IsSquare (p + q^2)) := by
  intro h
  rcases h with ⟨h1, h2⟩
  rcases h1 with ⟨a, ha⟩
  rcases h2 with ⟨b, hb⟩
  have h_eq1 : a^2 = p^2 + q := by
    nlinarith
  have h_eq2 : b^2 = p + q^2 := by
    nlinarith
  have h3 : a > p := by
    by_contra h
    push_neg at h
    have h4 : a ≤ p := by linarith
    have h5 : a^2 ≤ p^2 := by 
      nlinarith
    nlinarith [h_eq1, h4, hq]
  have h4 : b > q := by 
    by_contra h
    push_neg at h
    have h8 : b ≤ q := by linarith
    have h9 : b^2 ≤ q^2 := by 
      nlinarith
    have h10 : p + q^2 > q^2 := by linarith [show 0 < p by omega]
    nlinarith [h_eq2, h8, h10]
  have h7 : a < p + 1 := by 
    nlinarith [sq_nonneg (a - (p + 1 : ℕ)), sq_nonneg (b - (q + 1 : ℕ)), 
      h_eq1, h_eq2
    ]
  -- From h_eq1 and h_eq2
  have h8 : a = p := by 
    nlinarith
  -- From h_eq1 and h8 contradictory
  have h9 : q = 0 := by 
    nlinarith [h_eq1, h8]
  omega