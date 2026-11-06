import Mathlib

theorem number_theory_58639 (a b c : ℤ) (ha : 0 < a) (hb : b < 0) (hc : c < b)
    (hsum : a + b + c = 0) :
    ∃ k, k^2 = 2017 - a^3 * b - b^3 * c - c^3 * a ↔ (a, b, c) = (36, -12, -24) := by
  use 1009
  constructor
  · -- Assume $N=1009^2$.
    intro h_eq
    have ha1 : c = -a - b := by
      linarith
    rw [ha1] at h_eq
    have h_eq2 : a = 36 ∧ b = -12 := by
      have eq1 : 1009^2 = 2017 - a^3 * b - b^3 * (-a - b) - (-a - b) ^ 3 * a := by
        linarith
      have h2 : a ≤ 36 := by
        nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg (a - 36), sq_nonneg (b + 12), sq_pos_of_pos ha, sq_pos_of_neg (show b < 0 by linarith)]
      have h3 : a ≥ 1 := by nlinarith
      have h4 : b ≤ 0 := by nlinarith
      have h5 : b ≥ -24 := by
        nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg (a - 36), sq_nonneg (b + 12), sq_pos_of_pos ha, sq_pos_of_neg (show b < 0 by linarith)]
      interval_cases a <;> try { 
        omega
      }
      <;> try { 
          interval_cases b <;> norm_num at eq1 ⊢ 
          <;> try { 
              tauto 
          }
          <;> try { 
              nlinarith 
          }
      }
      <;> try { tauto }
    rcases h_eq2 with ⟨ha2, h3⟩
    have h4 : c = -24 := by
      rw [ha2, h3] at ha1
      linarith
    simp [ha2, h3, h4]
  · -- Assume $(a,b,c)=(36, -12, -24)$, prove $N =1009^2$.
    intro h_eq
    simp [Prod.mk.injEq] at h_eq
    rcases h_eq with ⟨rfl, rfl, rfl⟩
    norm_num