import Mathlib

variable (n : ℤ)

/- n can factor into a*b -/
abbrev is_factor (a b : ℤ) : Prop :=
  a > 0 ∧ b > 0 ∧ a * b = n

/- n can be expressed as x^2-y^2 -/
abbrev is_diff_of_squares (x y : ℤ) : Prop :=
  x ^ 2 - y ^ 2 = n

/- factor to diff_of_squares -/
abbrev f_4600 (p : ℤ × ℤ) : ℤ × ℤ :=
  ((p.1 + p.2) / 2, (p.1 - p.2) / 2)

/- diff_of_squares to factor -/
abbrev g1 (q : ℤ × ℤ) : ℤ × ℤ :=
  (q.1 + q.2, q.1 - q.2)

theorem number_theory_4600 (hn : Odd n) :
    (∀ a b : ℤ, is_factor n a b → g1 (f_4600 (a, b)) = (a, b)) ∧
    (∀ x y : ℤ, is_diff_of_squares n x y → f_4600 (g1 (x, y)) = (x, y)) := by

  constructor
  · -- First part
    intros a b h
    rcases h with ⟨ha_pos, hb_pos, hprod⟩
    have h1 : a % 2 = 1 ∨ a % 2 = 0 := by omega 
    have h2 : b % 2 = 1 ∨ b % 2 = 0 := by omega

    -- Show a and b are both odd.
    have h1' : a % 2 = 1 := by
      by_contra h
      push_neg at h 
      have h3 : a % 2 = 0 := by omega 
      have h4 : n % 2 = 0 := by
        have h5 : n = a * b := by linarith 
        rw [h5] 
        simp [Int.mul_emod, h3]
      have h5 : n % 2 = 1 := by
        obtain ⟨k, hk⟩ := hn 
        omega 
      omega

    have h2' : b % 2 = 1 := by
      by_contra h
      push_neg at h 
      have h3 : b % 2 = 0 := by omega 
      have h4 : n % 2 = 0 := by
        have h5 : n = a * b := by linarith 
        rw [h5] 
        simp [Int.mul_emod, h3]
      have h5 : n % 2 = 1 := by
        obtain ⟨k, hk⟩ := hn 
        omega 
      omega

    have h3 : (a + b) % 2 = 0 := by 
      omega

    have h4 : (a - b) % 2 = 0 := by 
      omega

    simp [g1, f_4600] at *
    have h7 : (a + b) / 2 + (a - b) / 2 = a := by 
      omega

    have h8 : (a + b) / 2 - (a - b) / 2 = b := by 
      omega

    simp_all [Prod.ext_iff, h7, h8]

  · -- Second part 
    intros x y h 
    simp [f_4600, g1] at *
    all_goals 
      ring_nf 
      <;> omega