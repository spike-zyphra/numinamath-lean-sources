import Mathlib

/- Let $n$ be an integer with $n \geqslant 2$. Does there exist a sequence $\left(a_{1}, \ldots, a_{n}\right)$ of positive integers with not all terms being equal such that the arithmetic mean of every two terms is equal to the geometric mean of some (one or more) terms in this sequence? (Estonia) -/
theorem number_theory_24021 (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℕ) (h_pos : ∀ i, 0 < a i)
    (h_not_equal : ∃ i j, a i ≠ a j)
    (h_mean : ∀ i j, ∃ s : Finset (Fin n), s.Nonempty ∧ (a i + a j : ℝ) / 2 = (∏ i in s, (a i : ℝ)) ^ (1 / (s.card : ℝ))) : False := by
  have _ : Fact (1 < n) := ⟨by omega⟩
  -- Suppose that $a_{1}, \ldots, a_{n}$ satisfy the required properties.
  -- Let $d=\operatorname{gcd}\left(a_{1} \ldots, a_{n}\right)$.
  let d := Finset.gcd (Finset.univ) a
  have hd_dvd (i : Fin n) : d ∣ a i := by
    simp [d]
    apply Finset.gcd_dvd
    simp
  -- If $d > 1$ then replace the numbers $a_{1}, \ldots, a_{n}$ by $\frac{a_{1}}{d}, \ldots, \frac{a_{n}}{d}$; all arithmetic and all geometric means will be divided by $d$, so we obtain another sequence satisfying the condition.
  -- Hence, without loss of generality, we can assume that $\operatorname{gcd}\left(a_{1} \ldots, a_{n}\right)=1$.
  wlog h_gcd : d = 1 generalizing a
  · apply this (fun i ↦ a i / d)
    · intro i
      apply Nat.div_pos
      · suffices (d ∣ a i) by exact Nat.le_of_dvd (h_pos i) this
        simp [d]
        apply Finset.gcd_dvd
        simp
      · simp [d]
        suffices ¬ (Finset.univ.gcd a = 0) by omega
        simp [Finset.gcd_eq_zero_iff]
        use ⟨0, by omega⟩
        specialize h_pos ⟨0, by omega⟩
        omega
    · peel h_not_equal
      contrapose! this
      rwa [Nat.div_left_inj] at this
      all_goals apply hd_dvd
    · peel h_mean with i j hs h
      refine ⟨h.left, ?_⟩
      have (i : Fin n) : ((a i / d : ℕ) : ℝ) = (a i : ℝ) / d := by
        rw [Nat.cast_div_charZero]
        apply hd_dvd
      simp [this]
      rw [Real.div_rpow, ← Real.rpow_natCast, ← Real.rpow_mul, mul_inv_cancel₀]
      rotate_left
      · simp [h.left.card_ne_zero]
      · positivity
      · positivity
      · positivity
      apply And.right at h
      simp at h ⊢
      rwa [← add_div, div_right_comm, div_left_inj']
      simp [d]
      simp [Finset.gcd_eq_zero_iff]
      use ⟨0, by omega⟩
      specialize h_pos ⟨0, by omega⟩
      omega
    · intro i
      apply Finset.gcd_dvd
      simp
    · apply Finset.gcd_div_eq_one (i := ⟨0, by omega⟩)
      · simp
      · specialize h_pos ⟨0, by omega⟩
        omega
  -- We show two numbers, $a_{m}$ and $a_{k}$ such that their arithmetic mean, $\frac{a_{m}+a_{k}}{2}$ is different from the geometric mean of any (nonempty) subsequence of $a_{1} \ldots, a_{n}$.
  -- That proves that there cannot exist such a sequence.
  absurd h_mean
  push_neg
  change ∃ m k, ∀ (s : Finset (Fin n)), s.Nonempty → (a m + a k : ℝ) / 2 ≠ (∏ i ∈ s, (a i : ℝ)) ^ (1 / (s.card : ℝ))
  -- Choose the index $m \in\{1, \ldots, n\}$ such that $a_{m}=\max \left(a_{1}, \ldots, a_{n}\right)$.
  let am := Finset.sup' (Finset.univ (α := Fin n)) (Finset.univ_nonempty) a
  obtain ⟨m, hm⟩ : ∃ m, a m = am := by
    simp [am]
    have := Finset.exists_mem_eq_sup' (s := Finset.univ (α := Fin n)) (Finset.univ_nonempty) a
    peel this with m h
    simp at h
    rw [h]
  use m
  -- Note that $a_{m} \geqslant 2$, because $a_{1}, \ldots, a_{n}$ are not all equal.
  have h1 : 2 ≤ a m := by
    obtain ⟨i, j, hij⟩ := h_not_equal
    have := h_pos i
    have := h_pos j
    have := Finset.le_sup' a (show i ∈ Finset.univ by simp)
    have := Finset.le_sup' a (show j ∈ Finset.univ by simp)
    omega
  -- Let $p$ be a prime divisor of $a_{m}$.
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (show a m ≠ 1 by omega)
  -- Let $k \in\{1, \ldots, n\}$ be an index such that $a_{k}=\max \left\{a_{i}: p \nmid a_{i}\right\}$.
  -- Due to $\operatorname{gcd}\left(a_{1} \ldots, a_{n}\right)=1$, not all $a_{i}$ are divisible by $p$, so such a $k$ exists.
  let s : Finset (Fin n) := Finset.filter (fun i ↦ ¬ p ∣ a i) (Finset.univ)
  have hs : s.Nonempty := by
    simp [s, Finset.filter_nonempty_iff]
    by_contra! h
    replace h : ∀ i ∈ Finset.univ, p ∣ a i := by
      simpa
    rw [← Finset.dvd_gcd_iff] at h
    change p ∣ d at h
    simp [h_gcd] at h
    simp [h, Nat.not_prime_one] at hp
  let ak := Finset.sup' _ hs a
  obtain ⟨k, hk1, hk2⟩ : ∃ k, a k = ak ∧ ¬ p ∣ a k := by
    simp [ak]
    have := Finset.exists_mem_eq_sup' (s := s) hs a
    peel this with k h
    simp at h
    simp [h.right]
    simp [s] at h
    exact h.left
  use k
  -- Note that $a_{m} > a_{k}$ because $a_{m} \geqslant a_{k}, p \mid a_{m}$ and $p \nmid a_{k}$.
  have h2 : a m > a k := by
    have := Finset.le_sup' a (show k ∈ Finset.univ by simp)
    by_contra! h
    replace h : a m = a k := by omega
    rw [← h] at hk2
    contradiction
  -- Let $b=\frac{a_{m}+a_{k}}{2}$; we will show that $b$ cannot be the geometric mean of any subsequence of $a_{1}, \ldots, a_{n}$.
  set b := (a m + a k : ℝ) / 2
  -- Consider the geometric mean, $g=\sqrt[t]{a_{i_{1}} \cdot \ldots \cdot a_{i_{t}}}$ of an arbitrary subsequence of $a_{1}, \ldots, a_{n}$.
  intro t ht
  set g := (∏ i ∈ t, (a i : ℝ)) ^ (1 / (t.card : ℝ))
  by_cases h_div : ∀ i ∈ t, ¬ p ∣ a i
  -- If none of $a_{i_{1}}, \ldots, a_{i_{t}}$ is divisible by $p$, then they are not greater than $a_{k}$, so $$ g=\sqrt[t]{a_{i_{1}} \cdot \ldots \cdot a_{i_{t}}} \leqslant a_{k} < \frac{a_{m}+a_{k}}{2}=b $$ and therefore $g \neq b$.
  · have h3 : ∀ i ∈ t, a i ≤ a k := by
      intro i hi
      convert Finset.le_sup' a (show i ∈ s by simp [s]; solve_by_elim)
    suffices g < b by linarith
    calc
      _ ≤ (∏ i ∈ t, (a k : ℝ)) ^ (1 / (t.card : ℝ)) := by
        simp only [g]
        gcongr
        solve_by_elim
      _ = (a k : ℝ) := by
        simp
        rw [← Real.rpow_natCast, ← Real.rpow_mul, mul_inv_cancel₀]
        · simp
        · simp [ht.card_ne_zero]
        · positivity
      _ < _ := by
        simp [b]
        rify at h2
        linarith
  -- Otherwise, if at least one of $a_{i_{1}}, \ldots, a_{i_{t}}$ is divisible by $p$, then $2 g=2 \sqrt{t} \sqrt{a_{i_{1}} \cdot \ldots \cdot a_{i_{t}}}$ is either not an integer or is divisible by $p$, while $2 b=a_{m}+a_{k}$ is an integer not divisible by $p$, so $g \neq b$ again.
  · push_neg at h_div
    suffices ¬ ∃ m : ℕ, ¬ p ∣ m ∧ 2 * g = m by
      contrapose! this
      use a m + a k
      constructor
      · rwa [← Nat.dvd_add_iff_right]
        assumption
      · simp [← this, b]
        ring
    push_neg
    intro m hm
    contrapose! hm
    apply_fun (fun x ↦ x ^ t.card) at hm
    rw [mul_pow] at hm
    simp [g] at hm
    conv at hm =>
      lhs; arg 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), inv_mul_cancel₀ (by simp [ht.card_ne_zero])]
    simp at hm
    norm_cast at hm
    apply Nat.Prime.dvd_of_dvd_pow (n := t.card) hp
    rw [← hm]
    apply Dvd.dvd.mul_left
    obtain ⟨i, hi1, hi2⟩ := h_div
    trans a i
    · assumption
    exact Finset.dvd_prod_of_mem _ hi1
