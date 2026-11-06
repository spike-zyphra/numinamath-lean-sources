import Mathlib

theorem number_theory_295773 (a : ℕ → ℕ) (ha : a 0 = 3 ^ 2012)
    (h : ∀ n, a (n + 1) = (Nat.digits 10 (a n)).sum) : a 9 = 9 := by

  -- for any n, a(n) is a multiple of 9
  have ha₁ (n : ℕ) : 9 ∣ a n := by
    induction n with
    | zero =>
      rw [ha]
      omega
    | succ n ih =>
      rw [h, ←Nat.nine_dvd_iff]
      exact ih


  have ha₂ (n : ℕ) : a n ≠ 0 := by
    induction n with
    | zero =>
      rw [ha]
      norm_num
    | succ n ih =>
      have (l : List ℕ) (hl : l ≠ []) (hl' : l.getLast hl ≠ 0) : l.sum ≠ 0 := by
        induction l with
        | nil => exact False.elim (hl rfl)
        | cons x xs ih =>
          simp
          intro hx
          rw [List.getLast_eq_getLastD] at hl'
          by_cases h: xs = []
          · absurd hl'
            rw [h]
            simp
            exact hx
          apply ih h
          cases xs
          · exact False.elim (h rfl)
          · rename_i y ys
            unfold List.getLastD at hl'
            simp at hl'
            exact hl'
      rw [h]
      apply this
      apply Nat.getLast_digit_ne_zero
      exact ih

  -- a 4 < 10
  have ha₃ : a 4 < 10 := by
    have _lemma (p n : ℕ) (h : p < 10^n) (h' : p ≠ 0) : (Nat.digits 10 p).sum < 10 * n := by
      have hlength : (Nat.digits 10 p).length ≤ n := by
        rw [Nat.digits_len 10 p (by simp) h']
        apply Order.add_one_le_of_lt
        exact Nat.log_lt_of_lt_pow h' h

      have hsum (r : ℕ) (l : List ℕ) (hl : l.length ≠ 0)
          (hl' : ∀i ∈ l, i < r) :
          l.sum < r * l.length := by
        induction l with
        | nil =>
          exact False.elim (hl rfl)
        | cons x xs ih =>
          simp at ih hl' hl
          simp
          by_cases hxs : xs = []
          · rw [hxs]
            simp [hl']
          specialize ih hxs hl'.2
          linarith

      apply lt_of_lt_of_le (hsum 10 (Nat.digits 10 p) ?_ ?_)
      linarith
      simp [Nat.digits_len 10 p (by simp) h']

      intro x hx
      exact Nat.digits_lt_base' hx

    have : a 1 < 10000 := by
      rw [h]
      exact _lemma (a 0) 1000 (by omega) (ha₂ 0)

    have : a 2 < 40 := by
      rw [h]
      exact _lemma (a 1) 4 (by omega) (ha₂ 1)

    have : a 3 < 13 := by
      rw [h]
      by_cases h₂ : a 2 < 10
      · rw [Nat.digits_of_lt _ _ (ha₂ 2) h₂]; simp
        linarith

      obtain ⟨p, q, hpq⟩ := show ∃p q: ℕ, Nat.digits 10 (a 2) = [p, q] by
        rw [Nat.digits_eq_cons_digits_div]; simp
        rw [Nat.digits_eq_cons_digits_div]; simp
        rw [show a 2 / 10 / 10 = 0 by omega]; simp
        repeat omega
      rw [hpq]; simp

      have hp : p < 10 := by
        apply Nat.digits_lt_base'
        rw [hpq]; simp
      have hq : q < 4 := by
        rw [Nat.digits_eq_cons_digits_div] at hpq
        simp at hpq
        have : Nat.ofDigits 10 [q] = a 2 / 10 := by
          rw [hpq.2.symm]
          exact Nat.ofDigits_digits 10 (a 2 / 10)
        simp at this
        repeat omega
      omega

    rw [h]
    interval_cases (a 3) <;> simp

  have ha₄ : a 4 = 9 := by
    specialize ha₁ 4
    specialize ha₂ 4
    omega

  rw [h, h, h, h, h, ha₄]
  simp
