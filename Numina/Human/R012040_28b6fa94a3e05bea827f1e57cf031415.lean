import Mathlib

/- 8. 52 Define the function $f(n)$ on the set of positive integers as follows:
$$f(n)=\left\{\frac{n}{2}, n+3\right.$$

when $n$ is even,
when $n$ is odd,
(1) Prove that for any positive integer $m$, the sequence
$$a_{0}=m, a_{1}=f(m), \cdots, a_{n}=f\left(a_{n-1}\right), \cdots$$

always contains a term that is 1 or 3.
(2) Among all positive integers, which $m$ make the above sequence necessarily contain 3? Which $m$ make the above sequence necessarily contain 1? -/
theorem number_theory_599878 {f: ℕ → ℕ}
  (hf: ∀ n, 0 < n → f n = if Even n then n/2 else n+3)
  {a: ℕ → ℕ} (ha: ∀i, a (i+1) = f (a i)):
  (∀m, 0 < m → a 0 = m → (∃ i, a i = 1 ∨ a i = 3)) ∧
  ( (0 < a 0 → (∃ i, a i = 3 ↔ 3 ∣ a 0) ) ∧
   (0 < a 0 → (∃ i, a i = 1 ↔ ¬ 3 ∣ a 0) ) ) := by

  -- let a_i0 be the minimal one.
  obtain ⟨i0, i0pos, hi0⟩: ∃ i0, 0 < i0 ∧
    (∀ i, 0 < i → a i0 ≤ a i) := by
    classical
    let s: Set ℕ := {m | ∃ i, 0 < i ∧ m = a i}
    have: s.Nonempty := by
      refine Set.nonempty_def.mpr ?_
      use (a 1), 1
      simp
    let n: ℕ := Nat.find this
    replace: n ∈ s := Nat.find_spec this
    rcases this with ⟨i0, hi0, hn⟩
    use i0,hi0
    intro i hi
    rw [← hn]
    apply Nat.find_min'
    use i,hi

  -- if 0 < a0, every a-term > 0.
  have apos (a0pos: 0 < a 0):
    ∀i, 0 < a i := by
    intro i
    induction' i with i ih
    · exact a0pos
    · rw [ha]
      specialize hf (a i) ih
      by_cases h: Even (a i)
      · rw [if_pos h] at hf
        rw [hf]
        refine Nat.div_pos ?_ (by norm_num)
        have: a i ≠ 1 := by
          rintro heq
          simp [heq] at h
        omega
      · rw [if_neg h] at hf
        simp [hf]

  -- now we can work out first part of the problem.
  -- say, if 0 < m and a0 = m, then contain a term is 1 or 3
  have a_min_1_or_3 (a0pos: 0 < a 0):
    a i0 = 1 ∨ a i0 = 3 := by
    -- we claim a i0 cannot exceed 3
    have h1: a i0 ≤ 3 := by
      by_contra! h1
      replace h1: a i0 ≥ 4 := by exact h1
      by_cases h: Even (a i0)
      · -- if ai0 even, a_{i0+1} = ai0 / 2 < ai0, contradiction.
        specialize ha (i0)
        rw [hf _ (apos a0pos i0), if_pos h] at ha
        specialize hi0 (i0+1) (by simp)
        rw [ha] at hi0
        absurd hi0
        push_neg
        refine Nat.bitwise_rec_lemma ?_
        omega
      · -- if ai0 odd, a_{n+2} = (ai0+3)/2 < ai0, also contradiction.
        have h2: Even (a (i0+1)) := by
          rw [ha i0, hf _ (apos a0pos i0), if_neg h]
          rw [Nat.not_even_iff_odd] at h
          apply h.add_odd ?_
          exact Nat.odd_iff.mpr rfl
        have := hf (a (i0+1)) (apos a0pos (i0+1))
        rw [if_pos h2, ← ha (i0+1)] at this
        rw [ha i0, hf _ (apos a0pos i0), if_neg h] at this
        specialize hi0 (i0+1+1) (by simp)
        rw [this] at hi0
        absurd hi0
        push_neg
        exact Nat.avg_lt_left h1
    -- 0 < ai0
    have h2: 0 < a i0 := apos a0pos _
    -- then suffices to prove a i0 ≠ 2
    have h3: a i0 ≠ 2 := by
      -- if ai0 = 2, a_{i0+1} = 1 < ai0, contradiction.
      rintro heq
      specialize ha i0
      rw [hf (a i0) h2, heq, if_pos (Nat.even_iff.mpr rfl)] at ha
      norm_num at ha
      specialize hi0 (i0+1) (by simp)
      absurd hi0
      rw [heq, ha]
      norm_num
    -- so ai0 can only be 1 or 3
    omega

  -- if 3 divide a0, then 3 divide all a-term
  have h_dvd_3 (a0pos: 0 < a 0) (a0dvd: 3 ∣ a 0):
    ∀i, 3 ∣ a i := by
    intro i
    induction' i with i ih
    · exact a0dvd
    · rw [ha i, hf (a i) (apos a0pos i)]
      by_cases h: Even (a i)
      · rw [if_pos h]
        rcases h with ⟨k, hk⟩
        simp only [hk, ← two_mul, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀]
        rw [hk, ← two_mul] at ih
        have: Nat.Coprime 3 2 := by norm_num
        exact this.dvd_of_dvd_mul_left ih
      · rw [if_neg h]
        apply ih.add dvd_rfl

  -- and if 3 not divide a0, then 3 not divide all a-term.
  have h_dvd_3' (a0pos: 0 < a 0) (not_a0dvd: ¬ 3 ∣ a 0):
    ∀i, ¬ 3 ∣ a i := by
    intro i
    induction' i with i ih
    · exact not_a0dvd
    · rw [ha i, hf (a i) (apos a0pos i)]
      by_cases h: Even (a i)
      · rw [if_pos h]
        have: a i = a i / 2 * 2 := by
          exact (Nat.div_two_mul_two_of_even h).symm
        rw [this] at ih
        by_contra!
        absurd ih
        apply this.mul_right
      · rw [if_neg h]
        by_contra!
        absurd ih
        exact Nat.dvd_add_self_right.mp this

  -- then we claim a i0 = 3 iff 3 divide a0
  have (a0pos: 0 < a 0): a i0 = 3 ↔ 3 ∣ a 0 := by
    constructor
    · intro h
      apply h_dvd_3 a0pos ?_ _
      by_contra!
      replace: ¬ 3 ∣ a i0 := h_dvd_3' a0pos this _
      simp [h] at this
    · intro h
      replace h: 3 ∣ a i0 := h_dvd_3 a0pos h _
      rcases (a_min_1_or_3 a0pos) with hh | hh
      · simp [hh] at h
      · exact hh

  -- nearly done.
  split_ands
  · intro m mpos hm
    rw [← hm] at mpos
    use i0
    apply a_min_1_or_3 mpos
  · intro a0pos
    use i0
    exact this a0pos
  · intro a0pos
    use i0
    rw [← this a0pos]
    replace := a_min_1_or_3 a0pos
    clear * - this
    aesop