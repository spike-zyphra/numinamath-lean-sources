import Mathlib
set_option maxHeartbeats 9999999999

lemma extracted_1 (n : ℕ) (h1 : n > 0) (p : ℕ) (h4 : Nat.Prime p) (k : ℕ) (pk : 0 < k)
  (bk : p ^ n - (p - 1) ^ n = 3 ^ k) : p % 3 = 2 := by
  have h_main : p % 3 = 2 := by
    have h₅ : p % 3 = 2 := by
      by_contra h
      -- We will show that if p % 3 ≠ 2, then a contradiction arises.
      have h₆ : p % 3 = 0 ∨ p % 3 = 1 := by
        -- Since p is a prime, p % 3 can only be 0, 1, or 2.
        omega
      cases h₆ with
      | inl h₆ =>
        -- Case: p % 3 = 0
        have h₇ : p = 3 := by
          -- Since p is a prime and p % 3 = 0, p must be 3.
          have h₈ : p % 3 = 0 := h₆
          have h₉ : p ≠ 0 := Nat.Prime.ne_zero h4
          have h₁₀ : 3 ∣ p := by
            omega
          have h₁₁ : p = 3 := by
            have h₁₂ := Nat.Prime.eq_one_or_self_of_dvd h4 3 h₁₀
            omega
          exact h₁₁
        -- Now we know p = 3, we can check the equation 3^n - 2^n = 3^k.
        rw [h₇] at bk
        have h₁₂ : (3 : ℕ) ^ n - (3 - 1 : ℕ) ^ n = 3 ^ k := by simpa using bk
        have h₁₃ : n > 0 := h1
        have h₁₄ : (3 : ℕ) ^ n - (2 : ℕ) ^ n = 3 ^ k := by simpa using h₁₂
        have h₁₅ : (3 : ℕ) ^ n % 3 = 0 := by
          -- Prove that 3^n ≡ 0 mod 3
          induction' h₁₃ with n h₁₃
          · simp
          · cases n with
            | zero => contradiction
            | succ n =>
              simp [Nat.pow_succ, Nat.mul_mod, Nat.pow_mod] at *
              <;> omega
        have h₁₆ : (2 : ℕ) ^ n % 3 = 1 ∨ (2 : ℕ) ^ n % 3 = 2 := by
          -- Prove that 2^n ≡ 1 or 2 mod 3
          have h₁₇ : ∀ n : ℕ, n > 0 → (2 : ℕ) ^ n % 3 = 1 ∨ (2 : ℕ) ^ n % 3 = 2 := by
            intro n hn
            induction' hn with n hn IH
            · norm_num
            · cases n with
              | zero =>
                norm_num at *
              | succ n =>
                cases IH with
                | inl IH =>
                  rw [pow_succ]
                  omega
                | inr IH =>
                  rw [pow_succ]
                  omega
          exact h₁₇ n h₁₃
        have h₁₇ : (3 : ℕ) ^ k % 3 = 0 := by
          -- Prove that 3^k ≡ 0 mod 3
          have h₁₈ : ∀ k : ℕ, k > 0 → (3 : ℕ) ^ k % 3 = 0 := by
            intro k hk
            induction' hk with k hk IH
            · norm_num
            · cases k with
              | zero => contradiction
              | succ k =>
                simp [Nat.pow_succ, Nat.mul_mod, Nat.pow_mod] at *
                <;> omega
          exact h₁₈ k pk
        simp at *
        have fc : 2^n < 3^n := by apply Nat.pow_lt_pow_left; (decide); exact Nat.not_eq_zero_of_lt h1
        omega
      | inr h₆ =>
        -- Case: p % 3 = 1
        have h₇ : (p - 1) ^ n % 3 = 0 := by
          -- Prove that (p - 1)^n ≡ 0 mod 3
          have h₈ : p % 3 = 1 := h₆
          have h₉ : (p - 1) % 3 = 0 := by
            have h₁₀ : p % 3 = 1 := h₈
            have h₁₁ : p ≥ 2 := Nat.Prime.two_le h4
            have h₁₂ : p - 1 ≥ 1 := by omega
            omega
          have h₁₀ : (p - 1) ^ n % 3 = 0 := by
            have h₁₁ : (p - 1) % 3 = 0 := h₉
            have h₁₂ : (p - 1) ^ n % 3 = 0 := by
              have h₁₃ : 3 ∣ (p - 1) := by omega
              have h₁₄ : 3 ∣ (p - 1) ^ n := by
                exact dvd_pow h₁₃ (by omega)
              omega
            exact h₁₂
          exact h₁₀
        have h₈ : p ^ n % 3 = 0 := by
          -- Prove that p^n ≡ 0 mod 3
          have h₉ : p ^ n % 3 = 0 := by
            have h₁₀ : p ^ n = 3 ^ k + (p - 1) ^ n := by
              have h₁₁ : p ^ n - (p - 1) ^ n = 3 ^ k := bk
              have h₁₂ : (p - 1) ^ n ≤ p ^ n := by
                exact Nat.pow_le_pow_of_le_left (by
                  have h₁₃ : p - 1 ≤ p := by
                    have h₁₄ : p ≥ 2 := Nat.Prime.two_le h4
                    omega
                  omega) n
              omega
            rw [h₁₀]
            have h₁₁ : (3 ^ k + (p - 1) ^ n) % 3 = 0 := by
              have h₁₂ : (3 ^ k : ℕ) % 3 = 0 := by
                have h₁₃ : ∀ k : ℕ, k > 0 → (3 : ℕ) ^ k % 3 = 0 := by
                  intro k hk
                  induction' hk with k hk IH
                  · norm_num
                  · cases k with
                    | zero => contradiction
                    | succ k =>
                      simp [Nat.pow_succ, Nat.mul_mod, Nat.pow_mod] at *
                      <;> omega
                exact h₁₃ k pk
              have h₁₃ : ((p - 1) ^ n : ℕ) % 3 = 0 := by omega
              omega
            omega
          exact h₉
        have h₉ : p % 3 = 1 := h₆
        have h₁₀ : p ^ n % 3 = 1 := by
          -- Prove that p^n ≡ 1 mod 3
          have h₁₁ : p % 3 = 1 := h₉
          have h₁₂ : p ^ n % 3 = 1 := by
            have h₁₃ : ∀ n : ℕ, n > 0 → p % 3 = 1 → p ^ n % 3 = 1 := by
              intro n hn hp
              induction' hn with n hn IH
              · simp [hp]
              · simp [pow_succ, Nat.mul_mod, hp, IH]
                <;> omega
            exact h₁₃ n h1 h₁₁
          exact h₁₂
        omega
    exact h₅
  exact h_main

lemma diff_of_powers_factor (x y : ℤ) (a k : ℕ) :
  x ^ (a * k) - y ^ (a * k)
    = (x ^ a - y ^ a) * ∑ i in Finset.range k, x ^ (a * (k - 1 - i)) * y ^ (a * i) := by
  have h_main : x ^ (a * k) - y ^ (a * k) = (x ^ a - y ^ a) * ∑ i in Finset.range k, x ^ (a * (k - 1 - i)) * y ^ (a * i) := by
    have h₁ : x ^ (a * k) - y ^ (a * k) = (x ^ a) ^ k - (y ^ a) ^ k := by
      rw [← pow_mul, ← pow_mul]
    rw [h₁]
    have h₂ : (x ^ a : ℤ) ^ k - (y ^ a : ℤ) ^ k = ((x ^ a : ℤ) - (y ^ a : ℤ)) * ∑ i in Finset.range k, (x ^ a : ℤ) ^ (k - 1 - i) * (y ^ a : ℤ) ^ i := by
      have h₃ : ∀ (X Y : ℤ) (k : ℕ), X ^ k - Y ^ k = (X - Y) * ∑ i in Finset.range k, X ^ (k - 1 - i) * Y ^ i := by
        intro X Y k
        have h₄ : X ^ k - Y ^ k = (X - Y) * ∑ i in Finset.range k, X ^ (k - 1 - i) * Y ^ i := by
          rw [eq_comm]
          -- Use the identity for the difference of powers
          have h₅ : (X - Y) * ∑ i in Finset.range k, X ^ (k - 1 - i) * Y ^ i = X ^ k - Y ^ k := by
            have h₆ : ∀ (X Y : ℤ) (n : ℕ), (X - Y) * ∑ i in Finset.range n, X ^ (n - 1 - i) * Y ^ i = X ^ n - Y ^ n := by
              intro X Y n
              have h₇ : (X - Y) * ∑ i in Finset.range n, X ^ (n - 1 - i) * Y ^ i = X ^ n - Y ^ n := by
                have aj := geom_sum₂_mul X Y n
                rw [mul_comm]
                clear * - aj
                have h_sum_reflect := Finset.sum_range_reflect (fun i => X ^ i * Y ^ (n - 1 - i)) n
                rw [← aj, ← h_sum_reflect]
                rw [← Finset.sum_attach]
                conv => right; rw [← Finset.sum_attach]
                congr
                ext a
                obtain ⟨a, b⟩ := a
                simp
                simp at b
                have ght : n - 1 - (n - 1 - a) = a := by omega
                rw [ght]
                simp
              exact h₇
            exact h₆ X Y k
          rw [h₅]
        rw [h₄]
      exact h₃ (x ^ a) (y ^ a) k
    rw [h₂]
    have h₄ : ∑ i in Finset.range k, (x ^ a : ℤ) ^ (k - 1 - i) * (y ^ a : ℤ) ^ i = ∑ i in Finset.range k, x ^ (a * (k - 1 - i)) * y ^ (a * i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h₅ : i < k := Finset.mem_range.mp hi
      have h₆ : (x ^ a : ℤ) ^ (k - 1 - i) = x ^ (a * (k - 1 - i)) := by
        rw [← pow_mul]
        <;> simp [mul_comm, Nat.mul_sub_left_distrib]
        <;> ring_nf
        <;> simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_sub_assoc]
        <;> omega
      have h₇ : (y ^ a : ℤ) ^ i = y ^ (a * i) := by
        rw [← pow_mul]
        <;> simp [mul_comm, Nat.mul_sub_left_distrib]
        <;> ring_nf
        <;> simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_sub_assoc]
        <;> omega
      rw [h₆, h₇]
    rw [h₄]
    <;> ring_nf
    <;> simp_all
    <;> omega
  exact h_main

lemma extracted_2 (p d j : ℕ) (pet : p % 3 = 2) (dd : 2 ≤ p) (ii : 1 < d) (dh : Odd d)
  (qq : p ^ d - (p - 1) ^ d = 3 ^ j) : False := by
  have ff : p^d ≥ (p-1)^d := by
    apply Nat.pow_le_pow_left
    clear * - dd; omega

  have h₁ : (p - 1) % 3 = 1 := by
    have h₁₁ : p % 3 = 2 := pet
    have h₁₂ : p ≥ 2 := dd
    have h₁₃ : p - 1 ≥ 1 := by omega
    have h₁₄ : (p - 1) % 3 = 1 := by
      have h₁₄₁ : p % 3 = 2 := h₁₁
      have h₁₄₂ : (p - 1) % 3 = 1 := by
        omega
      exact h₁₄₂
    exact h₁₄
  
  have h₂ : p ^ d % 3 = 2 := by
    have h₂₁ : p % 3 = 2 := pet
    have h₂₂ : p ^ d % 3 = 2 := by
      have h₂₃ : Odd d := dh
      have h₂₄ : p ^ d % 3 = 2 := by
        -- Use the fact that `d` is odd and `p % 3 = 2` to show `p^d ≡ 2 mod 3`
        have h₂₅ : d % 2 = 1 := by
          cases' dh with k hk
          omega
        have h₂₆ : p ^ d % 3 = 2 := by
          -- Use the fact that `d` is odd and `p % 3 = 2` to show `p^d ≡ 2 mod 3`
          have h₂₇ : p % 3 = 2 := pet
          have h₂₈ : ∀ n : ℕ, Odd n → p ^ n % 3 = 2 := by
            intro n hn
            have h₂₉ : p % 3 = 2 := pet
            have h₃₀ : p ^ n % 3 = 2 := by
              -- Use the fact that `d` is odd and `p % 3 = 2` to show `p^d ≡ 2 mod 3`
              have h₃₁ : Odd n := hn
              have h₃₂ : p ^ n % 3 = 2 := by
                -- Use the fact that `d` is odd and `p % 3 = 2` to show `p^d ≡ 2 mod 3`
                cases' h₃₁ with k hk
                rw [hk]
                rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
                simp [h₂₉, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
                <;> norm_num
                <;> ring_nf at *
                <;> omega
              exact h₃₂
            exact h₃₀
          exact h₂₈ d dh
        exact h₂₆
      exact h₂₄
    exact h₂₂
  
  have h₃ : (p - 1) ^ d % 3 = 1 := by
    have h₃₁ : (p - 1) % 3 = 1 := h₁
    have h₃₂ : (p - 1) ^ d % 3 = 1 := by
      have h₃₃ : ∀ n : ℕ, 0 < n → (p - 1) ^ n % 3 = 1 := by
        intro n hn
        have h₃₄ : (p - 1) % 3 = 1 := h₁
        have h₃₅ : (p - 1) ^ n % 3 = 1 := by
          rw [← Nat.mod_add_div ((p - 1) ^ n) 3]
          simp [h₃₄, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.pow_mod, Nat.add_mod]
          <;>
          induction' hn with n hn IH <;>
          simp_all [pow_succ, Nat.mul_mod, Nat.add_mod]
          <;>
          omega
        exact h₃₅
      exact h₃₃ d (by clear * - ii; linarith)
    exact h₃₂
  
  have h₄ : (p ^ d - (p - 1) ^ d) % 3 = 1 := by
    have h₄₁ : p ^ d % 3 = 2 := h₂
    have h₄₂ : (p - 1) ^ d % 3 = 1 := h₃
    have h₄₃ : (p ^ d - (p - 1) ^ d) % 3 = 1 := by
      have h₄₄ : p ^ d % 3 = 2 := h₄₁
      have h₄₅ : (p - 1) ^ d % 3 = 1 := h₄₂
      have h₄₆ : p ^ d > 0 := by
        apply Nat.pos_pow_of_pos d
        omega
      have h₄₇ : (p - 1) ^ d > 0 := by
        apply Nat.pos_pow_of_pos d
        have h₄₈ : p - 1 > 0 := by
          omega
        omega
      have h₄₈ : p ^ d - (p - 1) ^ d < p ^ d := by
        omega
      have h₄₉ : (p ^ d - (p - 1) ^ d) % 3 = 1 := by
        have h₄₁₀ : p ^ d % 3 = 2 := h₄₁
        have h₄₁₁ : (p - 1) ^ d % 3 = 1 := h₄₂
        have h₄₁₂ : (p ^ d - (p - 1) ^ d) % 3 = 1 := by
          omega
        exact h₄₁₂
      exact h₄₉
    exact h₄₃
  
  
  have h₅ : (3 ^ j) % 3 = 0 := by
    obtain _ | j := j
    pick_goal 2; (simp [Nat.pow_succ])
    norm_num at qq
    zify [ff, (by linarith : 1 ≤ p)] at qq
    have ex := geom_sum₂_mul (↑p : ℤ) (↑p - 1) d
    have we : (↑p : ℤ) ^ d - (↑p - 1) ^ d ≥ d := by
      rw [← ex]
      rw [(by ring : (↑p : ℤ) - (↑p - 1) = 1)]
      clear * - dd
      have xn := Finset.nsmul_eq_sum_const (1 : ℤ) d
      conv at xn => left; simp
      rw [xn]
      rw [ge_iff_le, mul_one]
      apply Finset.sum_le_sum
      simp
      intros i hi
      have d1 : (↑ p : ℤ)^i ≥ 1 := by
        norm_cast
        apply Nat.one_le_pow
        linarith
      have ab : (p - 1)^(d - 1 - i) ≥ 1 := by
        apply Nat.one_le_pow
        zify [(by linarith : p ≥ 1)]
        linarith
      zify [(by linarith : 1 ≤ p)] at ab
      clear * - d1 ab
      nlinarith
    linarith

  have h₆ : False := by
    have h₆₁ : (p ^ d - (p - 1) ^ d) % 3 = (3 ^ j) % 3 := by
      rw [qq]
    rw [h₄] at h₆₁
    rw [h₅] at h₆₁
    omega
  exact h₆

lemma rq (b : ∀ (d : ℕ), 1 < d → d ∣ 2 * aa → Nat.Prime d → d = 2) : (∀ (d : ℕ), 1 < d → d ∣ aa → Nat.Prime d → d = 2) := by
  intro d hd hdd hddp
  have h1 : d ∣ 2 * aa := by
    exact dvd_mul_of_dvd_right hdd 2
  exact b d hd h1 hddp

lemma iwo {n : ℕ} (g : n > 0) (h : ∀ d, 1 < d → d ∣ n → Even d) :
    ∃ k, n = 2 ^ k := by
  have i : ∀ d, 1 < d → d ∣ n → Nat.Prime d → d = 2 := by
    intros d hd dh dp
    have xa := h d hd dh
    exact (Nat.Prime.even_iff dp).mp xa
  clear h
  induction' n using induction_on_primes with p aa hp ih
  · norm_num at g
  · exists 0
  · have an := i p (by exact Nat.Prime.one_lt hp) (by exact Nat.dvd_mul_right p aa) hp
    subst p
    have qq := ih (by omega) (rq i)
    obtain ⟨qq, ww⟩ := qq
    exists (qq + 1)
    subst aa
    rw [Nat.pow_succ]
    ring

lemma pow_eq_one : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  constructor
  · -- Forward implication: if a^n = 1, then a = 1 or n = 0
    intro h
    by_cases hn : n = 0
    · -- If n = 0, then a^0 = 1 is trivial, so the goal becomes a = 1 ∨ (0 = 0)
      simp [hn] at h ⊢
      <;> tauto
    · -- Now consider the case n > 0.
      have h1 : n > 0 := by omega
      have h2 : a = 1 := by
        by_contra h2
        push_neg at h2
        have h3 : a > 0 := by
          by_contra h4
          push_neg at h4
          have h5 : a = 0 := by omega
          rw [h5] at h
          have h6 : 0 ^ n = 0 := by
            have h6 : n > 0 := h1
            simp [h6]
          rw [h6] at h
          omega
        have h4 : a > 1 := by omega
        have h5 : a ^ n > 1 := by
          apply Nat.one_lt_pow
          all_goals linarith
        linarith
      left
      exact h2
  · -- Backward implication: if a = 1 or n = 0, then a^n = 1
    rintro (ha | hn)
    · -- Case a = 1
      rw [ha]
      simp
    · -- Case n = 0
      rw [hn]
      simp

/- Find all positive integers $n$ such that there exists a prime number $p$, such that $p^n-(p-1)^n$ is a power of $3$.

Note. A power of $3$ is a number of the form $3^a$ where $a$ is a positive integer. -/
theorem number_theory_46251 (n : ℕ) :
    (n > 0 ∧ ∃ p, Nat.Prime p ∧ ∃ k, 0 < k ∧ p ^ n - (p - 1) ^ n = 3 ^ k) ↔ n = 2 := by
  symm; constructor
  · -- Verify n=2 satisfies the condition.
    intro k; subst n; simp
    exists 2; simp
    constructor; (decide)
    exists 1
  -- now prove n=2 is the only solution
  intro h'; rcases h' with ⟨h1,h2⟩; rcases h2 with ⟨p,h3⟩; rcases h3 with ⟨h4,h5⟩
  obtain ⟨k, ⟨pk, bk⟩⟩ := h5
  have pet : p % 3 = 2 := by apply extracted_1 n _ p _ k <;> assumption
  have dd : 2 ≤ p := by exact Nat.Prime.two_le h4
  have ee : p^n ≥ (p-1)^n := by
    apply Nat.pow_le_pow_left
    clear * - dd; omega
  have nx (d : ℕ) (hd : d ∣ n) : p^d - (p-1)^d ∣ p^n - (p-1)^n := by
    have ff : p^d ≥ (p-1)^d := by
      apply Nat.pow_le_pow_left
      clear * - dd; omega
    zify [ff, ee]
    obtain ⟨i, hi⟩ := hd
    have := diff_of_powers_factor p (p-1) d i
    rw [← hi] at this
    zify [(by clear * - dd; linarith : p ≥ 1)]
    rw [this]
    exact
      Int.dvd_mul_right (↑p ^ d - (↑p - 1) ^ d)
        (∑ i_1 ∈ Finset.range i, ↑p ^ (d * (i - 1 - i_1)) * (↑p - 1) ^ (d * i_1))
  -- prove n has no odd divisor
  have hs : ∀ d, 1 < d → d ∣ n → Even d := by
    by_contra y
    push_neg at y
    simp at y
    obtain ⟨d, ii, hd, dh⟩ := y
    have qq := nx d hd
    rw [bk] at qq
    rw [Nat.dvd_prime_pow (by decide : Nat.Prime 3)] at qq
    -- now we extract the exponent
    obtain ⟨j, hj, qq⟩ := qq
    clear * - dh dd pet qq ii
    apply extracted_2 p d j
    all_goals assumption
  have tt := iwo h1 hs
  obtain ⟨nh, tt⟩ := tt
  have ss : 1 ≤ p := by linarith
  have tt : p > p - 1 := by zify [ss]; linarith
  obtain _ | _ | nh := nh
  all_goals norm_num at tt; subst n
  · simp at bk
    rw [(by zify [ss, tt]; ring : p - (p - 1) = 1)] at bk
    symm at bk
    rw [pow_eq_one] at bk
    simp at bk
    subst k
    norm_num at pk
  · norm_num
  -- now we have to handle n ≥ 2
  ring_nf at *
  have aa := nx 2 (by clear * -; omega)
  rw [bk] at aa
  rw [Nat.dvd_prime_pow (by decide : Nat.Prime 3)] at aa
  obtain ⟨aa, aaa⟩ := aa
  -----------
  have bb := nx 4 (by clear * -; omega)
  rw [bk] at bb
  rw [Nat.dvd_prime_pow (by decide : Nat.Prime 3)] at bb
  obtain ⟨bb, bbb⟩ := bb
  obtain ⟨AAA, aaa⟩ := aaa
  obtain ⟨BBB, bbb⟩ := bbb
  have tq := Nat.pow_lt_pow_left tt (by decide : 2 ≠ 0)
  have tw := Nat.pow_lt_pow_left tt (by decide : 4 ≠ 0)
  zify [tq, ss] at aaa; zify [tw, ss] at bbb
  ring_nf at bbb
  rw [(by ring : -1 + (↑p * 4 - ↑p ^ 2 * 6) + ↑p ^ 3 * 4 = (↑p^2 - (↑ p - 1)^2) * (↑ p^2 + (↑ p - 1)^2)), aaa] at bbb
  ring_nf at aaa
  clear * - dd pet aaa bbb
  exfalso

  have h₁ : aa ≥ 1 := by
    by_contra h
    -- Assume aa = 0 and derive a contradiction.
    have h₂ : aa = 0 := by omega
    rw [h₂] at aaa
    norm_num at aaa
    norm_num at aaa
    have h₃ : (p : ℤ) = 1 := by
      omega
    have h₄ : (p : ℕ) = 1 := by
      norm_cast at h₃ ⊢
      <;> omega
    linarith
  
  have h₂ : (p : ℤ) * 2 = (3 : ℤ) ^ aa + 1 := by
    have h₂₁ : -1 + (↑p : ℤ) * 2 = 3 ^ aa := aaa
    have h₂₂ : (↑p : ℤ) * 2 = (3 : ℤ) ^ aa + 1 := by
      linarith
    exact h₂₂
  
  have h₃ : (p : ℕ) ≥ 2 := by
    have h₃₁ : (p : ℕ) ≥ 2 := by
      exact dd
    exact h₃₁
  
  have h₄ : (p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 ≠ (1 : ℤ) := by
    have h₄₁ : (p : ℕ) ≥ 2 := h₃
    have h₄₂ : (p : ℤ) ≥ 2 := by exact_mod_cast h₄₁
    have h₄₃ : (p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 > 1 := by
      nlinarith
    linarith
  
  have h₅ : (p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 ≡ 2 [ZMOD 3] := by
    rw [Int.ModEq]
    have h₅₁ : (p : ℕ) % 3 = 2 := pet
    have h₅₂ : (p : ℤ) % 3 = 2 := by
      norm_cast
      <;> simp [h₅₁]
      <;> omega
    have h₅₃ : (p : ℤ) % 3 = 2 := h₅₂
    have h₅₄ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2) % 3 = 2 := by
      have h₅₅ : (p : ℤ) % 3 = 2 := h₅₃
      have h₅₆ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2) % 3 = 2 := by
        have h₅₇ : (p : ℤ) % 3 = 2 := h₅₅
        have h₅₈ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2) % 3 = 2 := by
          have h₅₉ : (p : ℤ) % 3 = 2 := h₅₇
          have h₅₁₀ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2) % 3 = 2 := by
            norm_num [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h₅₉]
            <;>
            (try norm_num) <;>
            (try omega) <;>
            (try ring_nf at * <;> omega)
          exact h₅₁₀
        exact h₅₈
      exact h₅₆
    exact h₅₄
  
  have h₆ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ) % 3 = 2 := by
    rw [Int.ModEq] at h₅
    exact h₅
  
  have h₇ : aa = bb ∨ aa < bb ∨ aa > bb := by
    by_cases h₇ : aa = bb
    · exact Or.inl h₇
    · by_cases h₈ : aa < bb
      · exact Or.inr (Or.inl h₈)
      · have h₉ : aa > bb := by
          omega
        exact Or.inr (Or.inr h₉)
  
  have h₈ : False := by
    have h₈₁ : aa = bb ∨ aa < bb ∨ aa > bb := h₇
    rcases h₈₁ with (h₈₁ | h₈₁ | h₈₁)
    · -- Case: aa = bb
      have h₈₂ : aa = bb := h₈₁
      have h₈₃ : (3 : ℤ) ^ aa * ((↑p : ℤ) ^ 2 + (↑p - 1) ^ 2) = (3 : ℤ) ^ bb := by
        simpa [h₈₂] using bbb
      have h₈₄ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ) = 1 := by
        apply mul_left_cancel₀ (show (3 : ℤ) ^ aa ≠ 0 by positivity)
        rw [h₈₂] at h₈₃
        ring_nf at h₈₃ ⊢
        <;> nlinarith
      have h₈₅ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ) ≠ 1 := by
        simpa using h₄
      contradiction
    · -- Case: aa < bb
      have h₈₂ : aa < bb := h₈₁
      have h₈₃ : (3 : ℤ) ^ aa * ((↑p : ℤ) ^ 2 + (↑p - 1) ^ 2) = (3 : ℤ) ^ bb := by
        simpa using bbb
      have h₈₄ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ) % 3 = 2 := h₆
      have h₈₅ : ((3 : ℤ) ^ aa : ℤ) > 0 := by positivity
      have h₈₆ : ((3 : ℤ) ^ bb : ℤ) > 0 := by positivity
      have h₈₇ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ) ∣ (3 : ℤ) ^ bb := by
        use (3 : ℤ) ^ aa
        linarith
      have h₈₈ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ) ∣ (3 : ℤ) ^ bb := h₈₇
      have h₈₉ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ) % 3 = 2 := h₈₄
      have h₉₀ : ¬((3 : ℤ) ∣ ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ)) := by
        intro h₉₀
        have h₉₁ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ) % 3 = 0 := by omega
        omega
      have h₉₁ : ¬((3 : ℤ) ∣ ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ)) := h₉₀
      have h₉₂ : ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ) ∣ (3 : ℤ) ^ bb := h₈₈
      have h₉₃ : ¬((3 : ℤ) ∣ ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ)) := h₉₁
      have h₉₄ : False := by
        have h₉₅ : ((3 : ℤ) ∣ ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ)) := by
          -- Use the fact that if a number divides another, it must divide any of its factors.
          have h₉₅₁ : ((3 : ℤ) ∣ (3 : ℤ) ^ bb) := by
            exact dvd_pow_self (3 : ℤ) (by omega)
          have h₉₅₂ : ((3 : ℤ) ∣ ((p : ℤ) ^ 2 + ((p : ℤ) - 1) ^ 2 : ℤ)) := by
            have cheep : p^2 + (p - 1)^2 ∣ 3^bb := by zify [(by linarith : 1 ≤ p)]; assumption
            rw [Nat.dvd_prime_pow (by decide : Nat.Prime 3)] at cheep
            obtain ⟨zz, ff, gg⟩ := cheep
            obtain _ | zz := zz
            · clear * - gg dd; nlinarith
            zify [(by linarith : 1 ≤ p)] at gg
            rw [gg]; norm_cast
            rw [Nat.pow_succ]
            clear * -; exact Nat.dvd_mul_left 3 (3 ^ zz)
          exact h₉₅₂
        contradiction
      exact h₉₄
    · -- Case: aa > bb
      have h₈₂ : aa > bb := h₈₁
      have h₈₃ : (3 : ℤ) ^ aa * ((↑p : ℤ) ^ 2 + (↑p - 1) ^ 2) = (3 : ℤ) ^ bb := by
        simpa using bbb
      have h₈₄ : aa > 0 := by linarith
      have h₈₅ : (3 : ℤ) ^ aa * ((↑p : ℤ) ^ 2 + (↑p - 1) ^ 2) = (3 : ℤ) ^ bb := by simpa using bbb
      have h₈₆ : (3 : ℤ) ^ bb < (3 : ℤ) ^ aa * ((↑p : ℤ) ^ 2 + (↑p - 1) ^ 2) := by
        have h₈₇ : (3 : ℤ) ^ bb < (3 : ℤ) ^ aa := by
          exact pow_lt_pow_right (by norm_num) (by omega)
        have h₈₈ : (3 : ℤ) ^ aa > 0 := by positivity
        have h₈₉ : ((↑p : ℤ) ^ 2 + (↑p - 1) ^ 2 : ℤ) ≥ 1 := by
          have h₈₁₀ : (p : ℕ) ≥ 2 := h₃
          have h₈₁₁ : (p : ℤ) ≥ 2 := by exact_mod_cast h₈₁₀
          nlinarith
        nlinarith
      linarith
  exact h₈
