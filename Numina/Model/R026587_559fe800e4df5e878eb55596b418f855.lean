import Mathlib

open Real

theorem algebra_75757 {a : ℕ → ℝ} (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (ha' : ∀ n, 0 < a n) (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.range n, log (a i))
    (n m : ℕ) (hn : S n = S m) (hm : n ≠ m) : S (n + m) = 0 := by
  rcases ha with ⟨r, hr⟩
  have ha0_pos : 0 < a 0 := by 
    specialize ha' 0 
    simpa using ha'
  have hr_pos : 0 < r := by
    have ha1_pos : 0 < a 1 := by 
      specialize ha' 1 
      simpa using ha'
    have ha1_eq : a 1 = a 0 * r ^ 1 := by 
      specialize hr 1 
      simpa using hr 
    nlinarith [show 0 < a 0 from ha0_pos]
  have h2 : ∀ (k : ℕ), S k = (k : ℝ) * log (a 0) + (k * (k - 1) / 2 : ℝ) * log r := by
    intro k 
    rw [hS k]
    have h3 : ∀ (i : ℕ), log (a i) = log (a 0) + (i : ℝ) * log r := by
      intro i 
      have h4 : a i = a 0 * r ^ i := by 
        specialize hr i 
        simpa using hr 
      rw [h4]
      have h5 : 0 < a 0 := by
        specialize ha' 0 
        simpa using ha'
      have h7 : (0 : ℝ) < r ^ i := by
        have h9 : 0 < r := hr_pos
        positivity
      have h10 : 0 < a 0 * r ^ i := by positivity
      have h11 : log (a 0 * r ^ i) = log (a 0) + log (r ^ i) := by 
        rw [log_mul (by linarith) (by positivity)]
      have h12 : log (r ^ i) = (i : ℝ) * log r := by 
        simp [log_pow]
      rw [h11, h12]
    have h3k : ∀ (k : ℕ), ∑ i in Finset.range k, log (a i) = (k : ℝ) * log (a 0) + (k * (k - 1) / 2 : ℝ) * log r := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        rw [h3 k]
        field_simp at *
        ring
    simpa using h3k k
  have heq : (n : ℝ) * log (a 0) + (n * (n - 1) / 2 : ℝ) * log r = (m : ℝ) * log (a 0) + (m * (m - 1) / 2 : ℝ) * log r := by
    have h3 : S n = S m := hn
    rw [h2 n, h2 m] at h3 
    linarith
  have h4 : (n : ℝ) - (m : ℝ) ≠ 0 := by
    intro h
    have h5 : (n : ℝ) = (m : ℝ) := by linarith
    have h6 : n = m := by
      exact_mod_cast h5
    tauto
  have h4' : (n : ℝ) - (m : ℝ) = 0 ∨ (log (a 0) + ((n + m - 1 : ℝ) / 2) * log r = 0) := by 
    have heq' : (n : ℝ) * log (a 0) + (n * (n - 1) / 2 : ℝ) * log r = (m : ℝ) * log (a 0) + (m * (m - 1) / 2 : ℝ) * log r := heq
    have heq'' : (n - m : ℝ) * log (a 0) + ((n * (n - 1) - m * (m - 1)) / 2 : ℝ) * log r = 0 := by linarith [heq']
    have heq''': ((n - m : ℝ)) * (log (a 0) + ((n + m - 1 : ℝ) / 2) * log r) = 0 := by
      have heq4 : (n * (n - 1) - m * (m - 1) : ℝ) = (n - m : ℝ) * (n + m - 1 : ℝ) := by
        nlinarith
      rw [heq4] at heq''
      linarith
    cases (mul_eq_zero.1 heq''') with
    | inl h => 
      left 
      linarith 
    | inr h => 
      right 
      linarith 
  cases h4' with
  | inl h0 =>
    exfalso
    apply h4 
    linarith 
  | inr h0 =>
    have h9 : log (a 0) = - ((n + m - 1 : ℝ) / 2) * log r := by 
      linarith 
    have h10 : S (n + m) = (n + m : ℝ) * log (a 0) + ((n + m : ℝ) * ((n + m : ℝ) - 1) / 2 : ℝ) * log r := by 
      have h11 : ∀ (k : ℕ), S k = (k : ℝ) * log (a 0) + (k * (k - 1) / 2 : ℝ) * log r := h2 
      specialize h11 (n + m) 
      simpa using h11 
    rw [h10] 
    rw [h9] 
    ring_nf