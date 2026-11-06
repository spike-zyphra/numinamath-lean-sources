import Mathlib

/- 5. (German Mathematical Competition 2003-2004) Given the sequence $a_{1}, a_{2}, a_{3}, \cdots$ defined as follows:

$$

a_{1}=1, a_{2}=1, a_{3}=2, a_{n+3}=\frac{1}{a_{n}}\left(a_{n+1} a_{n+2}+7\right), n>0 \text {. }

$$


Prove: For all positive integers $n, a_{n}$ is an integer. -/
theorem algebra_205033 {a : ℕ → ℝ}
    (ha1 : a 0 = 1) (ha2 : a 1 = 1) (ha3 : a 2 = 2)
    (han : ∀ n, a (n + 3) = (a (n + 1) * a (n + 2) + 7) / a n) :
    ∀ n, ∃ m : ℤ, a n = m := by
  -- we have shifted the index to n = 0 to make it easier to work with
  -- first prove all a(n) are positive this'll allow easy division
  have hpos (n : ℕ) : 0 < a n := by
    -- use strong induction, positivity of a(n), a(n+1), a(n+2) easily prove positivity of a(n+3)
    induction' n using Nat.strong_induction_on with n hn
    match n with
    | 0 => rw [ha1]; norm_num
    | 1 => rw [ha2]; norm_num
    | 2 => rw [ha3]; norm_num
    | n + 3 =>
      rw [han]
      have := hn n (by omega)
      have := hn (n+1) (by omega)
      have := hn (n+2) (by omega)
      positivity
  -- next prove value of (a(n) + a(n+2))/a(n+1) stays same when you add 2 to indices
  have hdiv (n : ℕ) : (a n + a (n+2)) / (a (n+1)) = (a (n+2) + a (n+4)) / (a (n+3)) := by
    have := hpos n
    have := hpos (n+1)
    have := hpos (n+3)
    have := han n
    -- just subtract han on n and han on (n+1) (after clearing divisions)
    have h₁ : a (n+3) * a n = a (n+1) * a (n+2) + 7 := by
      rw [han n]
      field_simp
    have h₂ : a (n+4) * a (n+1) = a (n+2) * a (n+3) + 7 := by
      rw [han (n+1)]
      field_simp
    field_simp
    linear_combination h₁ - h₂
  -- determine value of a(3) using the recursion
  have ha4 : a 3 = 9 := by
    rw [han 0]
    rw [ha1, ha2, ha3]
    norm_num
  -- two auxilary lemma to easily prove parity of n is same as parity of n+2
  have aux_even {n : ℕ} (h : Even (n+2)) : Even n := by
    apply Nat.even_add.mp h |>.mpr
    use 1
  have aux_odd {n : ℕ} (h : Odd (n+2)) : Odd n := by
    apply Nat.odd_add.mp h |>.mpr
    use 1
  -- now for even n, a n + a (n + 2) = 3 * a (n+1), this is because of the ratio fact from before and at n = 0, the ratio is 3, use strong induction
  have heven (n : ℕ) (h: Even n) : a n + a (n + 2) = 3 * a (n+1) := by
    induction' n using Nat.strong_induction_on with n hn
    match n with
    | 0 => rw [ha1, ha3, ha2]; norm_num
    | 1 => simp at h
    | n + 2 =>
      have := hpos (n + 1)
      have := hpos (n + 3)
      have h' : Even n := aux_even h
      replace h' := hn n (by linarith) h'
      replace h' : (a n + a (n + 2)) / a (n + 1) = 3 := by field_simp; linarith
      rw [hdiv n] at h'
      field_simp at h'
      linarith
  -- for odd n, a n + a (n + 2) = 5 * a (n+1), again due to ratio fact and at n = 1, the ratio is 5, use strong induction
  have hodd (n : ℕ) (h: Odd n) : a n + a (n + 2) = 5 * a (n+1) := by
    induction' n using Nat.strong_induction_on with n hn
    match n with
    | 0 => simp at h
    | 1 => rw [ha2, ha3, ha4]; norm_num
    | n + 2 =>
      have := hpos (n + 1)
      have := hpos (n + 3)
      have h' : Odd n := aux_odd h
      replace h' := hn n (by linarith) h'
      replace h' : (a n + a (n + 2)) / a (n + 1) = 5 := by field_simp; linarith
      rw [hdiv n] at h'
      field_simp at h'
      linarith
  -- finally use strong induction to prove target, when n is even we have a(n) = 3 * a(n-1) - a(n-2), for odd n we have a(n) = 5 * a(n-1) - a(n-2). in both case previous values being integer guarantee a(n) is integer.
  rintro n
  induction' n using Nat.strong_induction_on with n hn
  match n with
  | 0 => rw [ha1]; use 1; norm_cast
  | 1 => rw [ha2]; use 1; norm_cast
  | n + 2 =>
    obtain ⟨x, hx⟩ := hn n (by linarith)
    obtain ⟨y, hy⟩ := hn (n+1) (by linarith)
    obtain h | h := Nat.even_or_odd (n+2)
    . have h' : Even n := aux_even h
      use 3 * y - x
      push_cast
      rw [← hx, ← hy]
      linarith [heven n h']
    . have h' : Odd n := aux_odd h
      use 5 * y - x
      push_cast
      rw [← hx, ← hy]
      linarith [hodd n h']