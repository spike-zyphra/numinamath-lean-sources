import Mathlib

/- 199. Prove that if a number $n$ is non-negative, then it can (and in a unique way!) be represented in the form $n=\frac{(x+y)^{2}+3 x+y}{2}$, where $x$ and $y$ are non-negative integers. -/
theorem number_theory_128892 {n : ℕ} :
    ∃! xy : ℕ × ℕ, n = ((xy.1 + xy.2) ^ 2 + 3 * xy.1 + xy.2) / 2 := by
  -- the problem is mainly related to f : x ↦ x * (x + 1) / 2, so let's define it and prove some facts
  let f (x : ℕ) := x * (x + 1) / 2
  -- first prove f (x + 1) = f(x) + x + 1, therefore f(x+1) > f(x) and so f is strictly increasing
  have hf_consec (x : ℕ) : f (x + 1) = f x + (x + 1) := by
    simp [f]
    rw [← Nat.add_mul_div_left _ _ (by norm_num)]
    congr
    ring
  have hf_incr_one (x : ℕ) : f x < f (x + 1) := by linarith [hf_consec x]
  have hf_mono : StrictMono f := by
    exact strictMono_nat_of_lt_succ hf_incr_one
  -- using last two facts, we can prove f(a) + b = f(c) + d with b ≤ a, d ≤ a proves a = c
  have hf_add_inj (a b c d : ℕ) (hab : b ≤ a) (hcd : d ≤ c) (h : f a + b = f c + d) :
    a = c := by
    by_contra h'
    obtain h' | h' := lt_or_gt_of_ne h'
    . change a + 1 ≤ c at h'
      replace h' : f (a + 1) ≤ f c := by
        exact (StrictMono.le_iff_le hf_mono).mpr h'
      rw [hf_consec] at h'
      linarith
    . change c + 1 ≤ a at h'
      replace h' : f (c + 1) ≤ f a := by
        exact (StrictMono.le_iff_le hf_mono).mpr h'
      rw [hf_consec] at h'
      linarith
  -- now we prove that following unique existance is enough
  suffices h : ∃! xy : ℕ × ℕ, xy.2 ≤ xy.1 ∧ n = (xy.1 * (xy.1 + 1) / 2) + xy.2 by
    -- extract a, b from the uniquness and show b, a-b are unique solution for our target
    obtain ⟨⟨a, b⟩, ⟨hab, hn⟩, hu⟩ := h
    simp at hab hn
    use ⟨b, a - b⟩
    and_intros <;> simp
    -- by manipulation, the equation is satisifed
    . rw [← Nat.add_mul_div_left _ _ (by norm_num)] at hn
      rw [hn]
      congr 1
      rw [show b + (a - b) = a by omega, mul_add, ← sq, mul_one]
      omega
    -- to prove unqiueness we use hf_add_inj
    . rintro p q hn'
      replace hn' : n = ((p + q) * (p + q + 1)) / 2 + p := by
        rw [← Nat.add_mul_div_left _ _ (by norm_num), hn']
        congr 1
        ring
      have ha : a = p + q := by
        change n = f a + b at hn
        change n = f (p + q) + p at hn'
        rw [hn] at hn'
        exact hf_add_inj a b (p+q) p hab (by linarith) hn'
      have hb : b = p := by
        rw [← ha] at hn'
        linarith
      simp [hb, ha]
  -- now we show unique existing of changed target
  apply existsUnique_of_exists_of_unique
  -- to prove existance, we first show there are k such that n < f(k)
  . simp only [Prod.exists]
    have hexists : ∃ k, n < f k := hf_mono.tendsto_atTop.eventually_gt_atTop n |>.exists
    -- then there is minimal A such that n < f(A), which is not zero
    let A := Nat.find hexists
    have ha_not_zero : A ≠ 0 := by
      rintro h
      have : n < f A := Nat.find_spec hexists
      simp [h, f] at this
    -- we will use A-1 and f(A-1) ≤ n then we will use n - f(A-1)
    use A - 1
    have h_f_minus_one_lt_n : f (A - 1) ≤ n := by
      apply le_of_not_lt
      apply Nat.find_min hexists
      omega
    use n - f (A - 1)
    -- this satisfy the conditions
    and_intros
    . suffices n + 1 ≤ f (A-1) + ((A-1) + 1) by omega
      rw [← hf_consec, show A - 1 + 1 = A by omega]
      have : n < f A := Nat.find_spec hexists
      linarith
    . change n = f (A - 1) + (n - f (A - 1))
      omega
    -- to prove uniqueness we use hf_add_inj again
  . rintro ⟨a, b⟩ ⟨c, d⟩ ⟨hab, hn⟩ ⟨hcd, hn'⟩
    simp at hab hn hcd hn'
    have hac : a = c := by
      apply hf_add_inj a b c d hab hcd (by rw [← hn, ← hn'])
    have hbd : b = d := by
      rw [hac] at hn
      linarith
    simp [hac, hbd]