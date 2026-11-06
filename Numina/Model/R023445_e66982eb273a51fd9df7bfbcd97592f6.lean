import Mathlib

open Real

/- Given positive real numbers $a$, $b$, and $c$ such that $a + b + c \geq 3$, determine the maximum value of the expression $P = \frac{a^3 + b^2 + c}{a^4 + b^3 + c^2}$. Prove that the maximum value is $1$, which is achieved when $a = b = c = 1$. -/
theorem inequalities_6696 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ 3) :
    (a ^ 3 + b ^ 2 + c) / (a ^ 4 + b ^ 3 + c ^ 2) ≤ 1 ∧
    ((a ^ 3 + b ^ 2 + c) / (a ^ 4 + b ^ 3 + c ^ 2) = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1) := by
  have h1 : 0 < a ^ 4 + b ^ 3 + c ^ 2 := by positivity
  constructor
  · -- Show that $P \leq 1$
    apply (div_le_iff₀ h1).mpr 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (c ^ 2 - 1),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
  constructor
  · -- Forward implication: if $P = 1$, then $a = 1 ∧ b = 1 ∧ c = 1$.
    intro h_eq 
    have h2 : a ^ 4 + b ^ 3 + c ^ 2 > 0 := by positivity 
    have h3 : a ^ 3 + b ^ 2 + c = a ^ 4 + b ^ 3 + c ^ 2 := by 
      have h_eq2 : (a ^ 3 + b ^ 2 + c) / (a ^ 4 + b ^ 3 + c ^ 2) = 1 := h_eq 
      field_simp at h_eq2 ⊢ 
      all_goals nlinarith 
    have h4 : a ^ 4 - a ^ 3 + b ^ 3 - b ^ 2 + c ^ 2 - c = 0 := by 
      nlinarith
    have h50 : (a - 1) ^ 2 ≥ 0 := sq_nonneg (a - 1)
    have h60 : (b - 1) ^ 2 ≥ 0 := sq_nonneg (b - 1)
    have h70 : (c - 1) ^ 2 ≥ 0 := sq_nonneg (c - 1)
    have ha2 : a = 1 := by
      have ha3 : (a - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
              ]
      nlinarith
    have hb2 : b = 1 := by
      have hb3 : (b - 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
              ]
      nlinarith
    have hc2 : c = 1 := by
      have hc3 : (c - 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
              ]
      nlinarith
    exact ⟨ha2, hb2, hc2⟩
  · -- Backward direction: if $a =1 ∧ b =1 ∧ c =1$, then $P =1$.
    rintro ⟨rfl, rfl, rfl⟩
    norm_num