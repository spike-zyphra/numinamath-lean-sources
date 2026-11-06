import Mathlib


/- some modulo calculation  -/
lemma lemma1 {M i: ℕ} (hM: 0 < M) (ipos: 1 ≤ i)
  (h2: (M+1 - (i-1) % (M+1)) % (M+1) = 0):
  (M + 1 - i % (M + 1)) % (M + 1) = M := by
  have h3: (M+1) - i % (M+1) = M - (i-1) % (M+1) := by
    change (M+1) - (i-1) % (M+1) ≡ 0 [MOD (M+1)] at h2
    have hh1: i = i - 1 + 1 := by simp [ipos]
    have hh2: (i - 1) % (M+1) = 0 := by
      rw [Nat.modEq_zero_iff_dvd] at h2
      have hh: M+1 ∣ (i-1) % (M+1) := by
        zify at h2 ⊢
        rw [Nat.cast_sub] at h2
        exact dvd_sub_self_left.mp h2
        apply le_of_lt (Nat.mod_lt (i - 1) (by simp))
      by_contra!
      replace: 0 < (i-1) % (M+1) := Nat.zero_lt_of_ne_zero this
      replace hh := Nat.le_of_dvd this hh
      absurd hh; push_neg
      apply Nat.mod_lt _ (by simp)
    nth_rw 1 [hh1, hh2, Nat.add_mod, hh2]
    simp [Nat.mod_eq_of_lt (show 1 < M+1 by simp [hM])]
  have h4: M+1 - (i-1) % (M+1) = M - (i-1) % (M+1) + 1 := by
    rw [add_comm M 1, Nat.add_sub_assoc, Nat.add_comm 1 _]
    apply Nat.le_of_lt_succ ?_
    rw [Nat.succ_eq_add_one, add_comm 1 M]
    apply Nat.mod_lt _ (by simp)
  replace h2: (M+1) - (i-1) % (M+1) ≡ M+1 [MOD (M+1)] := by
    apply h2.trans ?_
    exact Dvd.dvd.zero_modEq_nat dvd_rfl
  rw [h4] at h2
  symm
  nth_rw 1 [show M = M % (M+1) by simp, h3]
  exact (Nat.ModEq.add_right_cancel' 1 h2).symm

/- if n % m ≠ 0, 0 < m, then n % m = (n-1) % m + 1.  -/
lemma l_mod_sub_add_one_cancel {n m: ℕ}
  (hn: n % m ≠ 0) (hm: 0 < m): n % m = (n-1) % m + 1 := by
  have: (n-1) % m + 1 = ((n-1) % m + 1) % m := by
    nth_rw 2 [Nat.mod_eq_of_lt]
    suffices (n-1) % m + 1 ≠ m by
      apply lt_of_le_of_ne ?_ this
      replace: (n-1) % m < m := Nat.mod_lt _ hm
      omega
    rintro heq
    have h2: n = n-1 + 1 := by
      rw [Nat.sub_add_cancel]
      by_contra!
      replace: n = 0 := by omega
      simp [this] at hn
    replace: (n-1) % m = m - 1 := by
      omega
    have h3: 1 < m := by
      suffices m ≠ 1 by omega
      rintro meq
      rw [meq, Nat.mod_one] at hn
      simp at hn
    rw [h2] at hn
    nth_rw 2 [(Nat.mod_eq_of_lt h3).symm] at hn heq
    rw [← Nat.mod_add_mod, heq] at hn
    simp at hn
  rw [this, Nat.mod_add_mod, Nat.sub_add_cancel]
  by_contra!
  replace: n = 0 := by omega
  simp [this] at hn

/- some modulo calculation  -/
lemma lemma2 {M i: ℕ} (hM: 0 < M) (ipos: 1 ≤ i)
  (h1: ¬(M + 1 - (i - 1) % (M + 1)) % (M + 1) = 0):
  (M + 1 - (i - 1) % (M + 1)) % (M + 1) =
    (M + 1 - (i + 1 - 1) % (M + 1)) % (M + 1) + 1 := by
  by_cases heq: i % (M+1) = 0
  · simp only [add_tsub_cancel_right, heq,
    tsub_zero, Nat.mod_self, zero_add]
    change i ≡ 0 [MOD M+1] at heq
    replace heq: i-1+1 ≡ M+1 [MOD M+1] := by
      rw [Nat.sub_add_cancel ipos]
      apply heq.trans ?_
      exact Dvd.dvd.zero_modEq_nat dvd_rfl
    replace heq: i-1 ≡ M [MOD M+1] := by
      exact Nat.ModEq.add_right_cancel' 1 heq
    rw [heq, Nat.mod_succ M]
    simp [hM]
  · have h2: 0 < (M+1) - (i-1) % (M+1) := by
      simp only [tsub_pos_iff_lt]
      refine Nat.mod_lt (i - 1) (by simp)
    suffices h: (M+1 - i % (M+1)) = M+1 - (i-1) % (M+1) - 1 by
      rw [add_tsub_cancel_right, h, ← l_mod_sub_add_one_cancel h1 (by simp)]
    rw [Nat.sub_sub]
    congr 1
    exact l_mod_sub_add_one_cancel heq (by simp)


/- Let $a$ be an integer such that $a > 1$. Let $M$ be a positive integer such that $a^M-1 > 1$. Define $d = a^M-1$.
Let $x_1=1$ and, for $k \ge 1$, define the sequence $x_k$ by
$$ x_{k+1}= \begin{cases}x_{k}+d & \text { if } a \text { does not divide } x_{k} \\ x_{k} / a & \text { if } a \text { divides } x_{k}\end{cases} $$
Determine the greatest positive integer $n$ for which there exists an index $k$ such that $x_k$ is divisible by $a^n$. Show that this number is $M$. -/
theorem number_theory_637603 {a M d: ℕ} (ha: a > 1) (hM: 0 < M) (hM': a^M - 1 > 1)
  (d_def: d = a^M - 1):
  IsGreatest {n:ℕ | 0 < n ∧ ∃ x: ℕ → ℕ,
    (∃ k:ℕ, 1 ≤ k ∧ a^n ∣ x k) ∧ x 1 = 1 ∧
    ∀i, 0 < i → x (i+1) = if a ∣ x i then x i / a else x i + d} M := by

  -- we prove such sequence is cyclic: 1, a^M, a^(M-1), ..., a^1, 1, a^M, ...
  -- the period is M+1 (power index changes from 0 to M), so mod M+1 will appear.
  have hx {x: ℕ → ℕ} (x1eq: x 1 = 1)
    (x_succ: ∀i, 0 < i → x (i+1) = if a ∣ x i then x i / a else x i + d):
    ∀i, 0 < i → x i = a ^ ( ((M+1) - ((i-1) % (M+1))) % (M+1) ) := by
    intro i ipos
    induction' i,ipos using Nat.le_induction with i ipos ih
    · simp [x1eq]
    · by_cases h1: ((M+1) - (i-1) % (M+1)) % (M+1) = 0
      · specialize x_succ i ipos
        rw [if_neg (by simp [ih, h1, ha.ne'])] at x_succ
        have: x i + d = a^M := by
          simp only [ih, h1, pow_zero, d_def]
          omega
        rw [x_succ, this, Nat.add_sub_cancel, lemma1 hM ipos h1]
      · specialize x_succ i ipos
        have: a ∣ x i := by
          rw [ih]
          exact dvd_pow_self a h1
        rw [if_pos this] at x_succ
        rw [x_succ]
        apply Nat.div_eq_of_eq_mul_left (Nat.zero_lt_of_lt ha) ?_
        rw [ih, ← Nat.pow_succ, Nat.succ_eq_add_one]
        rw [lemma2 hM ipos h1]

  -- therefore obviously, greatest n for a^n divide x_k is M.
  rw [IsGreatest, upperBounds]
  simp only [Set.mem_setOf_eq, and_imp, forall_exists_index]
  constructor
  · set x: ℕ → ℕ := fun i =>
      if 0 < i then a ^ ( ((M+1) - ((i-1) % (M+1))) % (M+1) ) else 0 with x_def
    refine ⟨hM, x, ?_⟩
    split_ands
    · use 2
      have: (M+1 - 1 % (M+1)) % (M+1) = M := by
        rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (Nat.lt_add_of_pos_left hM), Nat.add_sub_cancel]
        simp [Nat.mod_eq_of_lt (Nat.lt_add_of_pos_left hM)]
      simp [x_def, this]
    · simp [x_def]
    · intro i ipos
      simp only [x_def, lt_add_iff_pos_left, add_pos_iff, ipos,
      zero_lt_one, or_self, ↓reduceIte, add_tsub_cancel_right]
      by_cases h1: ((M+1) - (i-1) % (M+1)) % (M+1) = 0
      · have: 1 + d = a^M := by
          rw [d_def]
          omega
        simp only [h1, pow_zero, Nat.dvd_one, ha.ne', ↓reduceIte, this]
        rw [lemma1 hM ipos h1]
      · simp only [dvd_pow_self a h1, ↓reduceIte]
        symm
        apply Nat.div_eq_of_eq_mul_left (Nat.zero_lt_of_lt ha) ?_
        rw [← Nat.pow_succ, Nat.succ_eq_add_one,
        lemma2 hM ipos h1, Nat.add_sub_cancel]
  · intro n npos x k kpos hdvd x1eq x_succ
    specialize hx x1eq x_succ k kpos
    rw [hx, pow_dvd_pow_iff
      (Nat.not_eq_zero_of_lt ha) (by simp [ha.ne'])] at hdvd
    suffices n < M+1 by exact Nat.le_of_lt_succ this
    refine lt_of_le_of_lt hdvd ?_
    apply Nat.mod_lt _ (by simp)