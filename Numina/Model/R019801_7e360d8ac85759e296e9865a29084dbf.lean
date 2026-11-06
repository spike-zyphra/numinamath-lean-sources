import Mathlib

theorem algebra_105634 {x : ℝ} {y : ℝ} (hy : y > 0) (A B : Finset ℝ)
    (hA : A = {x ^ 2 + x + 1, -x, -x - 1}) (hB : B = {-y, -y / 2, y + 1})
    (hAB : A = B) : x ^ 2 + y ^ 2 = 5 := by
  have h1 : (x ^ 2 + x + 1) ∈ A := by
    rw [hA]
    simp
  have h2 : (x ^ 2 + x + 1) ∈ B := by
    rw [hAB] at h1
    exact h1
  rw [hB] at h2
  simp at h2
  have h3 : (-x) ∈ A := by
    rw [hA]
    simp
  have h4 : (-x) ∈ B := by
    rw [hAB] at h3
    exact h3
  rw [hB] at h4
  simp at h4
  have h5 : (-x - 1) ∈ A := by
    rw [hA]
    simp
  have h6 : (-x - 1) ∈ B := by
    rw [hAB] at h5
    exact h5
  rw [hB] at h6
  simp at h6
  cases h2 with
  | inl h7 =>
    cases h4 with
    | inl h8 =>
      cases h6 with
      | inl h9 =>
        nlinarith
      | inr h9 =>
        cases h9 with
        | inl h9 =>
          nlinarith
        | inr h9 =>
          nlinarith
    | inr h8 =>
      cases h8 with
      | inl h8 =>
        cases h6 with
        | inl h9 =>
          nlinarith
        | inr h9 =>
          cases h9 with
          | inl h9 =>
            nlinarith
          | inr h9 =>
            nlinarith
      | inr h8 =>
        cases h6 with
        | inl h9 =>
          nlinarith
        | inr h9 =>
          cases h9 with
          | inl h9 =>
            nlinarith
          | inr h9 =>
            nlinarith
  | inr h7 =>
    cases h7 with
    | inl h7 =>
      cases h4 with
      | inl h8 =>
        cases h6 with
        | inl h9 =>
          nlinarith
        | inr h9 =>
          cases h9 with
          | inl h9 =>
            nlinarith
          | inr h9 =>
            nlinarith
      | inr h8 =>
        cases h8 with
        | inl h8 =>
          cases h6 with
          | inl h9 =>
            nlinarith
          | inr h9 =>
            cases h9 with
            | inl h9 =>
              nlinarith
            | inr h9 =>
              nlinarith
        | inr h8 =>
          cases h6 with
          | inl h9 =>
            nlinarith
          | inr h9 =>
            cases h9 with
            | inl h9 =>
              nlinarith
            | inr h9 =>
              nlinarith
    | inr h7 =>
      cases h4 with
      | inl h8 =>
        cases h6 with
        | inl h9 =>
          nlinarith
        | inr h9 =>
          cases h9 with
          | inl h9 =>
            nlinarith
          | inr h9 =>
            nlinarith
      | inr h8 =>
        cases h8 with
        | inl h8 =>
          cases h6 with
          | inl h9 =>
            nlinarith
          | inr h9 =>
            cases h9 with
            | inl h9 =>
              nlinarith
            | inr h9 =>
              nlinarith
        | inr h8 =>
          cases h6 with
          | inl h9 =>
            nlinarith
          | inr h9 =>
            cases h9 with
            | inl h9 =>
              nlinarith
            | inr h9 =>
              nlinarith