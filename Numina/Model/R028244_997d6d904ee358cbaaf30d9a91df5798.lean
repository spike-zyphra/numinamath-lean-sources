import Mathlib

theorem algebra_99587 {a b c d e : ℝ} (h1 : abs (a - b) = abs (b - c)) (h2 : abs (b - c) = abs (c - d))
    (h3 : abs (c - d) = abs (d - e)) (h4 : abs (d - e) = abs (e - a)):
    a = b ∧ b = c ∧ c = d ∧ d = e := by
  have h11 : (a - b) = (b - c) ∨ (a - b) = - (b - c) := by 
    cases' abs_eq_abs.1 h1 with h5 h6
    · -- Case a - b = b - c
      left 
      linarith 
    · -- Case a - b = -(b - c)
      right 
      linarith 
  have h12 : (b - c) = (c - d) ∨ (b - c) = - (c - d) := by 
    cases' abs_eq_abs.1 h2 with h5 h6 
    · -- Case b - c = c - d 
      left 
      linarith 
    · -- Case b - c = -(c - d)
      right 
      linarith 
  have h13 : (c - d) = (d - e) ∨ (c - d) = - (d - e) := by 
    cases' abs_eq_abs.1 h3 with h5 h6 
    · -- Case c - d = d - e 
      left 
      linarith 
    · -- Case c - d = -(d - e)
      right 
      linarith 
  have h14 : (d - e) = (e - a) ∨ (d - e) = - (e - a) := by 
    cases' abs_eq_abs.1 h4 with h5 h6 
    · -- Case d - e = e - a 
      left 
      linarith 
    · -- Case d - e = -(e - a)
      right 
      linarith 
  cases h11 with 
  | inl h11 =>
    cases h12 with
    | inl h12 =>
      cases h13 with
      | inl h13 =>
        cases h14 with
        | inl h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
        | inr h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
      | inr h13 =>
        cases h14 with
        | inl h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
        | inr h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
    | inr h12 =>
      cases h13 with
      | inl h13 =>
        cases h14 with
        | inl h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
        | inr h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
      | inr h13 =>
        cases h14 with
        | inl h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
        | inr h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
  | inr h11 =>
    cases h12 with
    | inl h12 =>
      cases h13 with
      | inl h13 =>
        cases h14 with
        | inl h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
        | inr h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
      | inr h13 =>
        cases h14 with
        | inl h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
        | inr h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
    | inr h12 =>
      cases h13 with
      | inl h13 =>
        cases h14 with
        | inl h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
        | inr h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
      | inr h13 =>
        cases h14 with
        | inl h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith 
        | inr h14 =>
          constructor 
          · linarith 
          constructor 
          · linarith 
          constructor 
          · linarith 
          · linarith