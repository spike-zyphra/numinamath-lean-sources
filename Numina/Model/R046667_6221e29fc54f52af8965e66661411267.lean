import Mathlib

theorem number_theory_4504 (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    IsLeast {d | 0 < d ∧ ∃ x y, d = x * a + y * b} (Int.gcd a b) := by
  constructor
  · -- Show that `gcd a b` is in the set 
    constructor
    · -- Show `gcd a b > 0`
      rcases h with (ha | hb)
      · -- Assume a ≠ 0
        have : a ≠ 0 := ha
        have : Int.gcd a b > 0 := by
          apply Int.gcd_pos_of_ne_zero_left
          exact this
        linarith
      · -- Assume b ≠ 0
        have : b ≠ 0 := hb
        have : Int.gcd a b > 0 := by
          apply Int.gcd_pos_of_ne_zero_right
          exact this
        linarith
    · -- Show existence of x y such that `gcd a b = x * a + y * b`
      use Int.gcdA a b, Int.gcdB a b
      rw [Int.gcd_eq_gcd_ab a b]
      all_goals linarith
  · -- Show that `Int.gcd a b` is the least in the set
    intro d hd
    rcases hd with ⟨hd_pos, ⟨x, y, h_eq⟩⟩
    have h1 : (Int.gcd a b : ℤ) ∣ (x * a + y * b) := by
      have h_gcd1 : (Int.gcd a b : ℤ) ∣ a := by
        apply Int.gcd_dvd_left
      have h_gcd2 : (Int.gcd a b : ℤ) ∣ b := by
        apply Int.gcd_dvd_right
      have h3 : (Int.gcd a b : ℤ) ∣ (x * a) := by
        apply dvd_trans h_gcd1
        use x
        all_goals ring_nf <;> omega
      have h4 : (Int.gcd a b : ℤ) ∣ (y * b) := by
        apply dvd_trans h_gcd2
        use y
        all_goals ring_nf <;> omega
      have h5 : (Int.gcd a b : ℤ) ∣ ((x * a) + (y * b)) := by
        apply dvd_add h3 h4
      rw [show (x * a + y * b) = ((x * a) + (y * b)) by ring]
      exact h5
    have h4 : (Int.gcd a b : ℤ) ∣ d := by
      rw [h_eq]
      exact h1
    have h5 : (Int.gcd a b : ℤ) ≤ d := by
      apply Int.le_of_dvd (by omega) h4
      all_goals omega
    linarith