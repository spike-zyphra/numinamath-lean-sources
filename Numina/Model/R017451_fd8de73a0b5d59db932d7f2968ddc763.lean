import Mathlib

theorem algebra_165348 {a d : ℝ} (h : ∑ i ∈ Finset.range m, (a + d * i) = ∑ i ∈ Finset.range n, (a + d * i)) (h' : m ≠ n) :
    ∑ i ∈ Finset.range (m + n), (a + d * i) = 0 := by
  have eq1 : ∑ i in Finset.range m, (a + d * i) = (m : ℝ) * a + d * ((m : ℝ) * (m - 1) / 2) := by
    have h2 : ∀ m : ℕ, ∑ i in Finset.range m, (a + d * i) = (m : ℝ) * a + d * ((m : ℝ) * (m - 1) / 2) := by
      intro m
      induction m with
      | zero =>
        simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        simp [add_assoc]
        <;> ring_nf
        <;> omega
    specialize h2 m
    simpa using h2
  have eq2 : ∑ i in Finset.range n, (a + d * i) = (n : ℝ) * a + d * ((n : ℝ) * (n - 1) / 2) := by
    have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (a + d * i) = (n : ℝ) * a + d * ((n : ℝ) * (n - 1) / 2) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [add_assoc]
        <;> ring_nf
        <;> omega
    specialize h2 n
    simpa using h2
  rw [eq1] at h
  rw [eq2] at h
  have eq3 : (m : ℝ) * a + d * ((m : ℝ) * (m - 1) / 2) = (n : ℝ) * a + d * ((n : ℝ) * (n - 1) / 2) := by
    exact_mod_cast h
  have eq4 : 2 * a + d * ((m + n - 1) : ℝ) = 0 := by
    have eq5 : (m : ℝ) * a + d * ((m : ℝ) * (m - 1) / 2) = (n : ℝ) * a + d * ((n : ℝ) * (n - 1) / 2) := eq3
    have eq6 : (m : ℝ) ≠ (n : ℝ) := by
      exact_mod_cast h'
    have eq7 : 2 * a * ((m : ℝ) - (n : ℝ)) + d * ((m : ℝ)^2 - (n : ℝ)^2 - ((m : ℝ) - (n : ℝ))) = 0 := by
      ring_nf at eq5 ⊢
      linarith
    have eq8 : (m : ℝ) - (n : ℝ) ≠ 0 := by
      exact sub_ne_zero_of_ne eq6
    have eq9 : (m : ℝ)^2 - (n : ℝ)^2 - ((m : ℝ) - (n : ℝ)) = ((m : ℝ) - (n : ℝ)) * ((m : ℝ) + (n : ℝ) - 1) := by
      ring
    have eq10 : ((m : ℝ) - (n : ℝ)) * (2 * a + d * ((m : ℝ) + (n : ℝ) - 1)) = 0 := by
      rw [eq9] at eq7
      linarith
    cases' (mul_eq_zero.mp eq10) with h2 h3
    · -- Case where (m - n) = 0
      exfalso
      exact eq8 (by linarith)
    · -- Case where the second factor is zero
      linarith
  have eq5 : ∑ i in Finset.range (m + n), (a + d * i) = ((m + n : ℝ) ) * a + d * (((m + n : ℝ) ) * ((m + n : ℝ) - 1) / 2) := by
    have h2 : ∀ k : ℕ, ∑ i in Finset.range k, (a + d * i) = (k : ℝ) * a + d * ((k : ℝ) * (k - 1) / 2) := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        simp [add_assoc]
        <;> ring_nf
        <;> omega
    specialize h2 (m + n)
    simpa using h2
  rw [eq5]
  have eq6 : 2 * a + d * ((m + n - 1) : ℝ) = 0 := eq4
  have eq7 : ((m + n : ℝ) ) * a + d * (((m + n : ℝ) ) * ((m + n : ℝ) - 1) / 2) = 0 := by
    have eq10 : (m + n : ℝ) * (2 * a + d * ((m + n - 1) : ℝ)) = 0 := by
      rw [show (2 * a + d * ((m + n - 1) : ℝ)) = (0 : ℝ) by linarith [eq6]]
      all_goals
        norm_num
    ring_nf at eq10 ⊢
    linarith
  linarith