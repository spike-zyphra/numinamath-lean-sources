import Mathlib

/- Does there exist a finite sequence of integers
$c_{1}, \ldots, c_{n}$ such that all the numbers
$a+c_{1}, \ldots, a+c_{n}$ are primes for
more than one but not infinitely many different integers $a$ ? -/
theorem number_theory_605932:
  ∃(n:PNat), ∃(c: Fin n → ℕ),
  Set.Finite {a:ℕ | ∀i, Nat.Prime (a + c i)} ∧
  {a:ℕ | ∀i, Nat.Prime (a + c i)}.ncard > 1 := by
  -- there exists such sequence.
  -- let n = 5
  use 5
  -- consider integers 0,2,8,14,26
  set c: Fin 5 → ℕ := fun i =>
    match i with
    | 0 => 0
    | 1 => 2
    | 2 => 8
    | 3 => 14
    | 4 => 26
    with c_def
  -- c has only 5 terms.
  have hci(i: Fin 5): c i = c 0 ∨ c i = c 1 ∨ c i = c 2 ∨
    c i = c 3 ∨ c i = c 4 := by
    have: i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      have h1: i.val ≤ 4 := Fin.is_le i
      have h2: i = i.val := (Fin.cast_val_eq_self i).symm
      interval_cases i.val
      all_goals
        norm_cast at h2; simp [h2]
    rcases this with hi | hi | hi | hi | hi
    all_goals simp [hi]
  have h0(a:ℕ): a + 0 = a + c 0 := rfl
  have h1(a:ℕ): a + 2 = a + c 1 := rfl
  have h2(a:ℕ): a + 8 = a + c 2 := rfl
  have h3(a:ℕ): a + 14 = a + c 3 := rfl
  have h4(a:ℕ): a + 26 = a + c 4 := rfl
  use c
  -- a+0, a+2, a+8, a+14, a+26 have pairwise different remainders modulo 5
  -- so one of them must = 0
  have h_amod5(a:ℕ): a+0 ≡ 0 [MOD 5] ∨ a+2 ≡ 0 [MOD 5] ∨ a+8 ≡ 0 [MOD 5] ∨
    a+14 ≡ 0 [MOD 5] ∨ a+26 ≡ 0 [MOD 5] := by
    have{m k: ℕ}(h: a ≡ m [MOD 5]):
      a + k ≡ m + k [MOD 5] := Nat.ModEq.add h rfl
    mod_cases ha: a % 5
    · left; apply Nat.ModEq.trans (this ha) rfl
    · right; right; right; left
      apply Nat.ModEq.trans (this ha) rfl
    · right; right; left
      apply Nat.ModEq.trans (this ha) rfl
    · right; left
      apply Nat.ModEq.trans (this ha) rfl
    · right; right; right; right
      apply Nat.ModEq.trans (this ha) rfl
  -- therefore one of a + c i is divisible by 5.
  have hdvd: ∀a:ℕ, ∃(i: Fin 5), 5 ∣ a + c i := by
    intro a
    have := h_amod5 a
    rw [h0, h1, h2, h3, h4] at this
    rcases this with hh | hh | hh | hh | hh
    all_goals rw [Nat.modEq_zero_iff_dvd] at hh
    use 0; use 1; use 2; use 3; use 4
  -- a can only be 3 or 5
  have ha: {a:ℕ | ∀i, Nat.Prime (a + c i)} = {3, 5} := by
    ext a; simp; constructor
    · intro h
      rcases (hdvd a) with ⟨i, hi⟩
      replace hi := (Nat.Prime.dvd_iff_eq
        (h i) (by norm_num)).mp hi
      -- if a+ci is prime, then 5 ∣ a+ci means a+ci = 5
      -- a2,a3,a4 > 5, they cannot add to 5.
      -- only possible solution is 0+a = 5 and 2+a = 5.
      -- therefore a = 5 or 3.
      rcases (hci i) with hhi | hhi | hhi | hhi | hhi
      all_goals simp [hhi, ← h0, ← h1, ← h2, ← h3, ← h4] at hi
      all_goals simp [hi]
    · rintro (aeq | aeq)
      all_goals
        intro i
        rcases (hci i) with hhi | hhi | hhi | hhi | hhi
        <;> simp [hhi, ← h0, ← h1, ← h2, ← h3, ← h4, aeq]
        -- when a=3, a+ci = 3,5,11,17,29. all prime.
        -- a=5, a+ci = 5,7,13,19,31. also prime.
        <;> norm_num
  -- so a = 3 or 5.
  -- satisfy "more than one but not infinitely many different integer a"
  simp [ha]