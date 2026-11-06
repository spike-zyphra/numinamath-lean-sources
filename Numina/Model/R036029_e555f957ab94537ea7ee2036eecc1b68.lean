import Mathlib

theorem algebra_10634 {a d : ℚ} {S : ℕ → ℚ}
    (hS : ∀ m, S m = ∑ i in Finset.range m, (a + d * i)) (hS1 : S m = 30) (hS2 : S (2 * m) = 100) :
    S (3 * m) = 210 := by

  have eq3 : ∀ n : ℕ, S n = (n : ℚ) * a + ((n : ℚ) * ((n : ℚ) - 1) / 2) * d := by
    intro n
    rw [hS n]
    have eq4 : ∀ n : ℕ, ∑ i in Finset.range n, (a + d * (i : ℚ)) =
        (n : ℚ) * a + ((n : ℚ) * ((n : ℚ) - 1) / 2) * d := by 
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp at *
        ring_nf
        <;> field_simp
        <;> ring 
    specialize eq4 n
    simpa using eq4
  have eq4 : S m = (m : ℚ) * a + ((m : ℚ) * ((m : ℚ) - 1) / 2) * d := by
    specialize eq3 m 
    simpa using eq3 
  have eq5 : S (2 * m) = (2 * m : ℚ) * a + ((2 * m : ℚ) * ((2 * m : ℚ) - 1) / 2) * d := by
    specialize eq3 (2 * m)
    simpa using eq3 
  have eq6 : S (3 * m) = (3 * m : ℚ) * a + ((3 * m : ℚ) * ((3 * m : ℚ) - 1) / 2) * d := by 
    specialize eq3 (3 * m)
    simpa using eq3
  have eq7 : (m : ℚ) * a + ((m : ℚ) * ((m : ℚ) - 1) / 2) * d = 30 := by 
    have eq8 : S m = 30 := hS1 
    rw [eq4] at eq8 
    linarith 
  have eq8 : (2 * m : ℚ) * a + ((2 * m : ℚ) * ((2 * m : ℚ) - 1) / 2) * d = 100 := by 
    have eq9 : S (2 * m) = 100 := hS2 
    rw [eq5] at eq9 
    linarith
  rw [eq6]
  nlinarith [sq_nonneg ((m : ℚ)), sq_nonneg ((m : ℚ) * (m : ℚ)), sq_nonneg ( (m : ℚ) * (d : ℚ) ), sq_nonneg ((m : ℚ) * (a : ℚ)), sq_nonneg ((d : ℚ)), sq_nonneg ((a : ℚ)), sq_nonneg ((m : ℚ) * 2 * (d : ℚ)), sq_nonneg ((m : ℚ) * 2 * (a : ℚ)), sq_pos_of_pos (show 0 < (2 : ℚ) by norm_num) ]