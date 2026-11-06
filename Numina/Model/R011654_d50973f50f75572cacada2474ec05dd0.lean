import Mathlib

theorem algebra_274133
  {a b c : ℝ} (hsum : a + b + c = 0) (hprod : a * b * c = 1) :
  ((a > 0) ∧ (b < 0) ∧ (c < 0)) ∨
  ((b > 0) ∧ (a < 0) ∧ (c < 0)) ∨
  ((c > 0) ∧ (a < 0) ∧ (b < 0)) := by
  have h2 : a < 0 ∨ b < 0 ∨ c < 0 := by
    by_contra h
    push_neg at h
    have ha1 : a ≥ 0 := h.1
    have hb1 : b ≥ 0 := h.2.1
    have hc1 : c ≥ 0 := h.2.2
    have ha2 : a = 0 := by
      nlinarith
    have hb2 : b = 0 := by
      nlinarith
    have hc2 : c = 0 := by
      nlinarith
    rw [ha2, hb2, hc2] at hprod
    nlinarith
  rcases h2 with h2 | h2 | h2
  · -- Assume a < 0
    have hbc : b * c < 0 := by
      have ha2 : a < 0 := h2
      have hprod2 : a * (b * c) > 0 := by
        calc
          a * (b * c) = a * b * c := by ring
          _ = 1 := hprod
          _ > 0 := by nlinarith
      nlinarith
    have hsum2 : b + c > 0 := by
      nlinarith
    have h3 : (b > 0 ∧ c < 0) ∨ (b < 0 ∧ c > 0) := by
      apply Or.elim (mul_neg_iff.mp hbc)
      · -- Case $b > 0 \land c < 0$
        intro h
        tauto
      · -- Case $b < 0 \land c > 0$
        intro h
        tauto
    cases h3 with
    | inl h3 =>
      -- b > 0 ∧ c < 0
      have hb1 : b > 0 := h3.1
      have hc1 : c < 0 := h3.2
      tauto
    | inr h3 =>
      -- b < 0 ∧ c > 0
      have hb1 : b < 0 := h3.1
      have hc1 : c > 0 := h3.2
      tauto
  · -- Assume b < 0
    have hac : a * c < 0 := by
      have hb1 : b < 0 := h2
      have hprod1 : a * c * b = 1 := by
        calc
          a * c * b = a * b * c := by ring
          _ = 1 := hprod
      have hprod2 : (a * c) * b > 0 := by
        nlinarith
      nlinarith
    have hsum2 : a + c > 0 := by
      nlinarith
    have h3 : (a > 0 ∧ c < 0) ∨ (a < 0 ∧ c > 0) := by
      apply Or.elim (mul_neg_iff.mp hac)
      · -- Case $a > 0 \land c < 0$
        intro h
        tauto
      · -- Case $a < 0 \land c > 0$
        intro h
        tauto
    cases h3 with
    | inl h3 =>
      -- a > 0 ∧ c < 0
      have ha1 : a > 0 := h3.1
      have hc1 : c < 0 := h3.2
      tauto
    | inr h3 =>
      -- a < 0 ∧ c > 0
      have ha1 : a < 0 := h3.1
      have hc1 : c > 0 := h3.2
      tauto
  · -- Assume c < 0
    have hab : a * b < 0 := by
      have hc1 : c < 0 := h2
      have hprod1 : a * b * c = 1 := hprod
      have hprod2 : a * b * c > 0 := by
        nlinarith
      have hprod3 : (a * b) * c > 0 := by
        linarith
      nlinarith
    have hsum2 : a + b > 0 := by
      nlinarith
    have h3 : (a > 0 ∧ b < 0) ∨ (a < 0 ∧ b > 0) := by
      apply Or.elim (mul_neg_iff.mp hab)
      · -- Case $a > 0 \land b < 0$
        intro h
        tauto
      · -- Case $a < 0 \land b > 0$
        intro h
        tauto
    cases h3 with
    | inl h3 =>
      -- a > 0 ∧ b < 0
      have ha1 : a > 0 := h3.1
      have hb1 : b < 0 := h3.2
      tauto
    | inr h3 =>
      -- a < 0 ∧ b > 0
      have ha1 : a < 0 := h3.1
      have hb1 : b > 0 := h3.2
      tauto