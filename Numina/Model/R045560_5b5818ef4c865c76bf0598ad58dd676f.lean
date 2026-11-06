import Mathlib

theorem number_theory_59693 (a b c : ℝ) (ha : a ≠ b) (hb : a ≠ c) (hc : b ≠ c) :
    (∃ n : ℤ, a ^ 3 / ((a - b) * (a - c)) + b ^ 3 / ((b - a) * (b - c)) + c ^ 3 / ((c - a) * (c - b)) = n) ↔ ∃ m : ℤ, (a - ⌊a⌋) + (b - ⌊b⌋) + (c - ⌊c⌋) = m := by
  constructor
  · -- Assume there's an integer n such that the expression equals n.
    rintro ⟨n, hn⟩
    have h1 : a - b ≠ 0 := by
      intro h
      apply ha
      linarith
    have h2 : a - c ≠ 0 := by
      intro h
      apply hb
      linarith
    have h3 : b - a ≠ 0 := by
      intro h
      apply ha
      linarith
    have h4 : b - c ≠ 0 := by
      intro h
      apply hc
      linarith
    have h5 : c - a ≠ 0 := by
      intro h
      apply hb
      linarith
    have h6 : c - b ≠ 0 := by
      intro h
      apply hc
      linarith
    have eq1 : a ^ 3 / ((a - b) * (a - c)) + b ^ 3 / ((b - a) * (b - c)) + c ^ 3 / ((c - a) * (c - b)) = a + b + c := by
      field_simp [(show (a - b) ≠ 0 by assumption), (show (a - c) ≠ 0 by assumption), (show (b - a) ≠ 0 by assumption), (show (b - c) ≠ 0 by assumption), (show (c - a) ≠ 0 by assumption), (show (c - b) ≠ 0 by assumption)]
      ring
    have eq2 : (a + b + c : ℝ) = (n : ℝ) := by
      linarith [eq1, hn]
    use (n - (⌊a⌋ + ⌊b⌋ + ⌊c⌋))
    have eq4 : (a - ⌊a⌋) + (b - ⌊b⌋) + (c - ⌊c⌋) = (a + b + c) - (⌊a⌋ + ⌊b⌋ + ⌊c⌋ : ℝ) := by
      ring
    have eq6 : (a + b + c : ℝ) = (n : ℝ) := eq2
    rw [eq4]
    have hn1 : (n : ℝ) = (n : ℝ) := by rfl
    simp at hn1 ⊢
    all_goals
      try { linarith }
      try { tauto }
  · -- Assume there's an integer m such that the sum of fractional parts equals m.
    rintro ⟨m, hm⟩
    have h1 : a - b ≠ 0 := by
      intro h
      apply ha
      linarith
    have h2 : a - c ≠ 0 := by
      intro h
      apply hb
      linarith
    have h3 : b - a ≠ 0 := by
      intro h
      apply ha
      linarith
    have h4 : b - c ≠ 0 := by
      intro h
      apply hc
      linarith
    have h5 : c - a ≠ 0 := by
      intro h
      apply hb
      linarith
    have h6 : c - b ≠ 0 := by
      intro h
      apply hc
      linarith
    have eq1 : a ^ 3 / ((a - b) * (a - c)) + b ^ 3 / ((b - a) * (b - c)) + c ^ 3 / ((c - a) * (c - b)) = a + b + c := by
      field_simp [(show (a - b) ≠ 0 by assumption), (show (a - c) ≠ 0 by assumption), (show (b - a) ≠ 0 by assumption), (show (b - c) ≠ 0 by assumption), (show (c - a) ≠ 0 by assumption), (show (c - b) ≠ 0 by assumption)]
      ring
    have eq4 : (a - ⌊a⌋) + (b - ⌊b⌋) + (c - ⌊c⌋) = (a + b + c) - (⌊a⌋ + ⌊b⌋ + ⌊c⌋ : ℝ) := by
      ring
    have eq5 : (a + b + c : ℝ) = (m : ℝ) + (⌊a⌋ + ⌊b⌋ + ⌊c⌋ : ℝ) := by
      linarith [hm, eq4]
    use m + ⌊a⌋ + ⌊b⌋ + ⌊c⌋
    have eq7 : a ^ 3 / ((a - b) * (a - c)) + b ^ 3 / ((b - a) * (b - c)) + c ^ 3 / ((c - a) * (c - b)) = (a + b + c) := by
      linarith [eq1]
    rw [eq7]
    have eq11 : (a + b + c : ℝ) = (↑(m + ⌊a⌋ + ⌊b⌋ + ⌊c⌋ : ℤ)) := by
      have eq12 : (m + ⌊a⌋ + ⌊b⌋ + ⌊c⌋ : ℝ) = (m : ℝ) + (⌊a⌋ : ℝ) + (⌊b⌋ : ℝ) + (⌊c⌋ : ℝ) := by
        exact_mod_cast rfl
      have eq13 : (a + b + c : ℝ) = (m : ℝ) + (⌊a⌋ : ℝ) + (⌊b⌋ : ℝ) + (⌊c⌋ : ℝ) := by
        linarith [eq5]
      have eq14 : (↑(m + ⌊a⌋ + ⌊b⌋ + ⌊c⌋ : ℤ) : ℝ) = (m : ℝ) + (⌊a⌋ : ℝ) + (⌊b⌋ : ℝ) + (⌊c⌋ : ℝ) := by
        simp [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
        <;> ring_nf
      linarith [eq13, eq14]
    linarith [eq11]