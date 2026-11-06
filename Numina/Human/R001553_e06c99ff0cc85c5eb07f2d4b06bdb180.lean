import Mathlib

set_option maxHeartbeats 0

/- Let $2 \mathbb{Z}+1$ denote the set of odd integers. Find all functions $f: \mathbb{Z} \rightarrow 2 \mathbb{Z}+1$ satisfying  $$ f(x+f(x)+y)+f(x-f(x)-y)=f(x+y)+f(x-y) $$  for every $x, y \in \mathbb{Z}$. -/
theorem algebra_24565 (f : ℤ → ℤ) :
    ((∀ x, Odd (f x)) ∧ ∀ x y : ℤ, f (x + f x + y) + f (x - f x - y) = f (x + y) + f (x - y)) ↔ (∃ d : ℕ, ∃ k : ℤ, ∃ (l : List ℤ), Odd d ∧ l.length = d ∧ (∀ l' ∈ l, Odd l') ∧ ∀ n : ℤ, f n = (2 * k * (n / ↑d) * d + l[(n % ↑d).natAbs]! * d : ℤ)) := by
  -- Lemma 1: If g : ℤ → ℤ is a function of positive period A and B, then g has a period of gcd(A, B).
  have lemma_1 (g : ℤ → ℤ) (A B : ℤ) (hA : A ≠ 0) (hB : B ≠ 0) : (∀ x : ℤ, g (x + A) = g x) ∧ (∀ x : ℤ, g (x + B) = g x) → (∀ x : ℤ, g (x + A.gcd B) = g x) := by
    rintro ⟨hA, hB⟩
    replace hA (x : ℤ) (m : ℕ) : g (x + m * A) = g x := by
      induction m with
      | zero =>
        simp
      | succ m hm =>
        calc
          g (x + (m + 1) * A) = g (x + m * A + A) := by ring_nf
          _ = g (x + m * A) := by rw [hA]
          _ = g x := by apply hm
    replace hA (x m : ℤ) : g (x + m * A) = g x := by
      by_cases h : 0 ≤ m
      . specialize hA x m.natAbs
        simp [Int.natAbs_of_nonneg h] at hA
        simp [hA]
      . specialize hA (x + m * A) (-m).natAbs
        rw [Int.natAbs_of_nonneg (show 0 ≤ -m by omega)] at hA
        ring_nf at hA ⊢
        linarith only [hA]
    replace hB (x : ℤ) (n : ℕ) : g (x + n * B) = g x := by
      induction n with
      | zero =>
        simp
      | succ n hn =>
        calc
          g (x + (n + 1) * B) = g (x + n * B + B) := by ring_nf
          _ = g (x + n * B) := by rw [hB]
          _ = g x := by apply hn
    replace hB (x n : ℤ) : g (x + n * B) = g x := by
      by_cases h : 0 ≤ n
      . specialize hB x n.natAbs
        simp [Int.natAbs_of_nonneg h] at hB
        simp [hB]
      . specialize hB (x + n * B) (-n).natAbs
        rw [Int.natAbs_of_nonneg (show 0 ≤ -n by omega)] at hB
        ring_nf at hB ⊢
        linarith only [hB]
    have h₀ := @Int.gcd_dvd_iff A B (A.gcd B)
    simp at h₀
    obtain ⟨m, n, h₀⟩ := h₀
    intro x
    nth_rewrite 1 [mul_comm] at h₀
    nth_rewrite 2 [mul_comm] at h₀
    rw [h₀, <-add_assoc, hB, hA]
  -- Lemma 2: If g : ℤ → ℤ is a function and t, s are non-zero integers such that Δ_{ts}g = Δ_tΔ_s g = 0, then Δ_t g = 0.
  have lemma_2 (g : ℤ → ℤ) (s t : ℕ) (spos : 0 < s) (tpos : 0 < t) (hts : ∀ x : ℤ, g (x + t * s) = g x) (htt : ∀ x : ℤ, g (x + t + t) - g (x + t) = g (x + t) - g x) : ∀ x : ℤ, g (x + t) - g x = 0 := by
    have h₀ (x : ℤ) (k : ℕ) : g (x + (k + 1) * t) - g (x + k * t) = g (x + t) - g (x) := by
      induction k with
      | zero =>
        simp
      | succ k hk =>
        calc
          g (x + (k + 1 + 1) * t) - g (x + (k + 1) * t) = g (x + k * t + t + t) - g (x + k * t + t) := by ring_nf
          _ = g (x + t) - g x := by rw [htt]; ring_nf at hk ⊢; rw [hk]
    have h₁ (x : ℤ) : 0 = s * (g (x + t) - g x) := by
      calc
        0 = g (x + t * s) - g x := by simp [hts]
        _ = ∑ i in Finset.range s, (g (x + (i + 1) * t) - g (x + i * t)) := by
          norm_cast
          rw [Finset.sum_range_sub (fun i => g (x + (i * t : ℕ)))]
          simp
          ac_rfl
        _ = ∑ i in Finset.range s, (g (x + t) - g x) := by
          apply Finset.sum_congr
          rfl
          intro i
          intro hi
          rw [h₀]
        _ = s * (g (x + t) - g x) := by
          rw [Finset.sum_const]
          simp
    simp [show s ≠ 0 by omega] at h₁
    exact h₁
  -- Lemma 3: For any prime p, the p-adic value of lcm (a, b) is equal to either that of a or b.
  have lemma_3 (a b p : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) [hp : Fact p.Prime] : padicValNat p (a.lcm b) = padicValNat p a ∨ padicValNat p (a.lcm b) = padicValNat p b := by
    have g₀ : a ∣ a.lcm b := Nat.dvd_lcm_left a b
    have g₁ : b ∣ a.lcm b := Nat.dvd_lcm_right a b
    apply exists_eq_mul_left_of_dvd at g₀
    apply exists_eq_mul_left_of_dvd at g₁
    obtain ⟨c₀, g₀⟩ := g₀
    obtain ⟨c₁, g₁⟩ := g₁
    have glcm : a.lcm b > 0 := by
      apply Nat.lcm_pos
      assumption'
    have g₃ : c₀ ≠ 0 := by
      by_contra!
      rw [this, zero_mul] at g₀
      linarith
    replace g₃ : c₀ ≥ 1 := by
      omega
    have g₄ : c₁ ≠ 0 := by
      by_contra!
      rw [this, zero_mul] at g₁
      linarith
    replace g₄ : c₁ ≥ 1 := by
      omega
    have g₆ : padicValNat p (a.lcm b) = padicValNat p c₀ + padicValNat p a := by
      rw [g₀]
      apply padicValNat.mul
      omega
      omega
    have g₇ : padicValNat p (a.lcm b) = padicValNat p c₁ + padicValNat p b := by
      rw [g₁]
      apply padicValNat.mul
      omega
      omega
    have h : padicValNat p c₀ = 0 ∨ padicValNat p c₁ = 0 := by
      by_contra!
      obtain ⟨g₆, g₇⟩ := this
      replace g₆ : 1 ≤ padicValNat p c₀ := by
        omega
      replace g₇ : 1 ≤ padicValNat p c₁ := by
        omega
      replace g₆ : p ∣ c₀ := by
        rw [show p = p ^ 1 by simp]
        rwa [padicValNat_dvd_iff_le]
        omega
      replace g₇ : p ∣ c₁ := by
        rw [show p = p ^ 1 by simp]
        rwa [padicValNat_dvd_iff_le]
        omega
      apply exists_eq_mul_right_of_dvd at g₆
      obtain ⟨d₀, g₆⟩ := g₆
      rw [g₆, mul_assoc] at g₀
      apply exists_eq_mul_right_of_dvd at g₇
      obtain ⟨d₁, g₇⟩ := g₇
      rw [g₇, mul_assoc] at g₁
      have g₉ : a ∣ a.lcm b / p := by
        calc
          a ∣ d₀ * a := by apply Nat.dvd_mul_left
          _ ∣ a.lcm b / p := by apply Nat.dvd_div_of_mul_dvd; rw [g₀]
      have g₁₀ : b ∣ a.lcm b / p := by
        calc
          b ∣ d₁ * b := by apply Nat.dvd_mul_left
          _ ∣ a.lcm b / p := by apply Nat.dvd_div_of_mul_dvd; rw [g₁]
      have g₁₂ : a.lcm b ∣ a.lcm b / p := by
        apply Nat.lcm_dvd
        assumption'
      replace g₁₂ : a.lcm b ≤ a.lcm b / p := by
        apply Nat.le_of_dvd
        rw [g₀, mul_comm, Nat.mul_div_cancel]
        have h : d₀ > 0 := by
          by_contra!
          have h : d₀ = 0 := by
            omega
          rw [h, mul_zero] at g₆
          omega
        apply Nat.mul_pos
        assumption'
        apply Nat.Prime.pos
        exact hp.out
      replace false_eq : a.lcm b * 2 < a.lcm b * 2 := by
        calc
          a.lcm b * 2 ≤ a.lcm b * p := by apply Nat.mul_le_mul_left; apply Nat.Prime.two_le; exact hp.out
          _ ≤ a.lcm b / p * p := by apply Nat.mul_le_mul_right; exact g₁₂
          _ = a.lcm b := by rw [Nat.div_mul_cancel]; rw [g₀]; apply Nat.dvd_mul_right
          _ < a.lcm b * 2 := by omega
      linarith
    obtain g₉ | g₁₀ := h
    left
    rw [g₉] at g₆
    rw [g₆, zero_add]
    right
    rw [g₁₀] at g₇
    rw [g₇, zero_add]
  -- Break the goal into two implications.
  apply Iff.intro
  . -- Solve for the functions that satisfy the conditions.
    rintro ⟨hOdd, hf₀⟩
    -- Let a = x + y and rewrite the equation.
    have hf₁ (x a : ℤ) : f (a + f x) - f a = f (2 * x - a - f x + f x) - f (2 * x - a - f x) := by
      specialize hf₀ x (a - x)
      ring_nf at hf₀ ⊢
      linarith only [hf₀]
    -- Show that Δ_{kf(x)}f(b) = Δ_{kf(x)}f(2x - b - kf(x)) for all k ∈ ℤ.
    have hf₂ (x b : ℤ) (k : ℕ) : f (b + k * f x) - f b = f (2 * x - b - k * f x + k * f x) - f (2 * x - b - k * f x) := by
      induction k with
      | zero =>
        simp
      | succ k hk =>
        calc
          f (b + (k + 1) * f x) - f b = (f (b + k * f x) - f b) + (f (b + (k + 1) * f x) - f (b + k * f x)) := by ring_nf
          _ = (f (2 * x - b - k * f x + k * f x) - f (2 * x - b - k * f x)) + (f (2 * x - b - k * f x - f x + f x) - f (2 * x - b - k * f x - f x)) := by rw [hk, hf₁]; ring_nf
          _ = f (2 * x - b - (k + 1) * f x + (k + 1) * f x) - f (2 * x - b - (k + 1) * f x) := by ring_nf
    replace hf₂ (x b k : ℤ) : f (b + k * f x) - f b = f (2 * x - b - k * f x + k * f x) - f (2 * x - b - k * f x) := by
      by_cases kpos : 0 ≤ k
      . specialize hf₂ x b k.natAbs
        simp [Int.natAbs_of_nonneg kpos] at hf₂
        simp [hf₂]
      . specialize hf₂ x (b + k * f x) (-k).natAbs
        rw [Int.natAbs_of_nonneg (show 0 ≤ -k by omega)] at hf₂
        ring_nf at hf₂ ⊢
        linarith only [hf₂]
    -- Show that Δ_{lcm(f(x), f(y))}f(b) = Δ_{lcm(f(x), f(y))}f(b + 2(y - x)) for all x, y ∈ ℤ.
    have hf₃ (x y b : ℤ) : f (b + (f x).lcm (f y)) - f b = f (b + 2 * (y - x) + (f x).lcm (f y)) - f (b + 2 * (y - x)) := by
      let L := (f x).lcm (f y)
      have hLx : ∃ k : ℤ, L = k * f x := by
        use L / f x
        rw [Int.ediv_mul_cancel]
        simp [L]
        apply Int.dvd_lcm_left
      have hLy : ∃ k : ℤ, L = k * f y := by
        use L / f y
        rw [Int.ediv_mul_cancel]
        simp [L]
        apply Int.dvd_lcm_right
      rw [show (f x).lcm (f y) = L by simp only [L]]
      obtain ⟨kx, hkx⟩ := hLx
      obtain ⟨ky, hky⟩ := hLy
      calc
        f (b + L) - f b = f (b + kx * f x) - f b := by rw [hkx]
        _ = f (2 * x - b) - f (2 * x - b - L) := by rw [hf₂, <-hkx]; ring_nf
        _ = f (2 * x - b - ky * f y + ky * f y) - f (2 * x - b - ky * f y) := by rw [hky]; ring_nf
        _ = f (b + 2 * (y - x) + L) - f (b + 2 * (y - x)) := by rw [hf₂, <-hky]; ring_nf
    -- Let Q = lcm(f(0), f(1)).
    let Q := (f 0).lcm (f 1)
    -- Show that f(x + Q) - f(x) = f(x + 2k + Q) - f(x + 2k), i.e., Δ_Q f(x) = Δ_Q f(x + 2k), for all k ∈ ℤ.
    have hf₄ (x : ℤ) := hf₃ 0 1 x
    simp [show (f 0).lcm (f 1) = Q by simp only [Q]] at hf₄
    replace hf₄ (x : ℤ) (k : ℕ) : f (x + Q) - f x = f (x + 2 * k + Q) - f (x + 2 * k) := by
      induction k with
      | zero =>
        simp
      | succ k hk =>
        calc
          f (x + Q) - f x = f (x + 2 * k + Q) - f (x + 2 * k) := by apply hk
          _ = f (x + 2 * (k + 1) + Q) - f (x + 2 * (k + 1)) := by rw [hf₄]; ring_nf
    replace hf₄ (x k : ℤ) : f (x + Q) - f x = f (x + 2 * k + Q) - f (x + 2 * k) := by
      by_cases kpos : 0 ≤ k
      . specialize hf₄ x k.natAbs
        simp [Int.natAbs_of_nonneg kpos] at hf₄
        simp [hf₄]
      . specialize hf₄ (x + 2 * k) (-k).natAbs
        rw [Int.natAbs_of_nonneg (show 0 ≤ -k by omega)] at hf₄
        ring_nf at hf₄ ⊢
        linarith only [hf₄]
    -- Show that g(0) = g(-Q).
    have hf₅ : f Q - f 0 = f 0 - f (-Q) := by
      specialize hf₂ 0 0 (Q / f 0)
      rw [Int.ediv_mul_cancel] at hf₂
      simp at hf₂
      simp [hf₂]
      apply Int.dvd_lcm_left
    -- Show that Q ≠ 0.
    have hQzero : Q ≠ 0 := by
      apply Nat.lcm_ne_zero
      apply ne_of_gt
      all_goals
        simp
        by_contra!
      . absurd hOdd 0
        simp [this]
      . absurd hOdd 1
        simp [this]
    -- Show that Q is odd.
    have hQOdd : Odd (Q : ℤ) := by
      by_contra! hQ
      norm_cast at hQ
      simp [Even] at hQ
      obtain ⟨q, hQ⟩ := hQ
      rw [<-mul_two, mul_comm] at hQ
      simp [Q] at hQ
      have hQ₀ : f 0 ∣ 2 * q := by
        zify at hQ
        rw [<-hQ]
        apply Int.dvd_lcm_left
      replace hQ₀ : f 0 ∣ q := by
        apply IsCoprime.dvd_of_dvd_mul_left at hQ₀
        exact hQ₀
        rw [Int.isCoprime_iff_gcd_eq_one]
        let d := (f 0).gcd 2
        have hd : d = (f 0).gcd 2 := rfl
        have hd' : d ∣ 2 := by
          rw [hd]
          apply gcd_dvd_right
        rw [<-hd]
        replace hd' : d ≤ 2 := by
          apply Nat.le_of_dvd (by norm_num) hd'
        interval_cases d
        . replace hd : 2 ∣ f 0 := by
            calc
              (2 : ℤ) ∣ (0 : ℕ) := by norm_num
              _ ∣ f 0 := by nth_rewrite 1 [hd]; apply gcd_dvd_left
          rw [<-even_iff_two_dvd] at hd
          absurd hOdd 0
          simp [hd]
        . rfl
        . replace hd : 2 ∣ f 0 := by
            rw [show (2 : ℤ) = (2 : ℕ) by simp, hd]
            apply gcd_dvd_left
          rw [<-even_iff_two_dvd] at hd
          absurd hOdd 0
          simp [hd]
      have hQ₁ : f 1 ∣ 2 * q := by
        zify at hQ
        rw [<-hQ]
        apply Int.dvd_lcm_right
      replace hQ₁ : f 1 ∣ q := by
        apply IsCoprime.dvd_of_dvd_mul_left at hQ₁
        exact hQ₁
        rw [Int.isCoprime_iff_gcd_eq_one]
        let d := (f 1).gcd 2
        have hd : d = (f 1).gcd 2 := rfl
        have hd' : d ∣ 2 := by
          rw [hd]
          apply gcd_dvd_right
        rw [<-hd]
        replace hd' : d ≤ 2 := by
          apply Nat.le_of_dvd (by norm_num) hd'
        interval_cases d
        . replace hd : 2 ∣ f 1 := by
            calc
              (2 : ℤ) ∣ (0 : ℕ) := by norm_num
              _ ∣ f 1 := by nth_rewrite 1 [hd]; apply gcd_dvd_left
          rw [<-even_iff_two_dvd] at hd
          absurd hOdd 1
          simp [hd]
        . rfl
        . replace hd : 2 ∣ f 1 := by
            rw [show (2 : ℤ) = (2 : ℕ) by simp, hd]
            apply gcd_dvd_left
          rw [<-even_iff_two_dvd] at hd
          absurd hOdd 1
          simp [hd]
      have hQ₂ : (f 0).lcm (f 1) ∣ q := by
        apply Nat.lcm_dvd
        . zify
          rw [abs_dvd]
          exact hQ₀
        . zify
          rw [abs_dvd]
          exact hQ₁
      rw [hQ] at hQ₂
      replace hQ₂ : q = 0 := by
        by_contra! hQ₃
        replace hQ₃ : 0 < q := by
          omega
        have hQ₄ : 2 * q ≤ q := by
          apply Nat.le_of_dvd hQ₃ hQ₂
        omega
      rw [show (f 0).lcm (f 1) = Q by simp only [Q], hQ₂] at hQ
      omega
    -- Show that Δ_Q f(x) is a constant, so Q is a quasi-period of f.
    have hf₆ : ∃ G : ℤ, ∀ x : ℤ, f (x + Q) - f x = G := by
      use f Q - f 0
      intro x
      by_cases xEven : Even x
      . obtain ⟨k, hk⟩ := xEven
        rw [<-mul_two, mul_comm] at hk
        rw [hk]
        specialize hf₄ 0 k
        ring_nf at hf₄ ⊢
        exact hf₄.symm
      . simp at xEven
        have hQ' : Even (x + Q) := Odd.add_odd xEven hQOdd
        simp [Even] at hQ'
        obtain ⟨q, hQ'⟩ := hQ'
        rw [<-mul_two, mul_comm] at hQ'
        calc
          f (x + Q) - f x = f 0 - f (-Q) := by rw [hf₄ x (-q), mul_neg, <-hQ']; ring_nf
          _ = f Q - f 0 := by rw [hf₅]
    -- Show that f has some minimal positive quasi-period T.
    have hf₇ : ∃ T > 0, (∃ G, ∀ x : ℤ, f (x + T) - f x = G) ∧ (∀ T', (T' > 0 ∧ ∃ G, ∀ x : ℤ, f (x + T') - f x = G) → T ≤ T') := by
      let S := {T : ℕ | T > 0 ∧ ∃ G, ∀ x : ℤ, f (x + T) - f x = G}
      have hS₀ : S.Nonempty := by
        simp [Set.Nonempty]
        use Q
        simp [S]
        exact ⟨by omega, hf₆⟩
      use! ((sInf S : ℕ) : ℤ)
      simp [-and_imp]
      replace hS₀ := Nat.sInf_mem hS₀
      rw [Set.mem_setOf] at hS₀
      simp only [true_and, hS₀]
      intro T' hT'
      have hT'' : T'.natAbs ∈ S := by
        rw [Set.mem_setOf]
        simp [Int.natAbs_of_nonneg (le_of_lt hT'.1), -ne_eq]
        exact ⟨by omega, hT'.2⟩
      have hS₁ := Nat.sInf_le hT''
      zify at hS₁
      rw [<-Int.natCast_natAbs] at hS₁
      simp [abs, Int.natAbs_of_nonneg (le_of_lt hT'.1)] at hS₁
      exact hS₁
    obtain ⟨T, Tpos, ⟨G, hf₇⟩, hf₆'⟩ := hf₇
    -- Show that T is odd.
    have TOdd : Odd T := by
      by_contra! hT
      have g₀ (x : ℤ) : f (x + 1 + T) - f (x + 1) = f (x + T) - f x := by
        rw [hf₇, hf₇]
      replace g₀ (x : ℤ) : f (x + T + 1) - f (x + T) = f (x + 1) - f x := by
        specialize g₀ x
        ring_nf at g₀ ⊢
        linarith only [g₀]
      have g₁ (x : ℤ) : f (x + 1 + Q) - f (x + 1) = f (x + Q) - f x := by
        obtain ⟨G, hf₆⟩ := hf₆
        rw [hf₆, hf₆]
      replace g₁ (x : ℤ) : f (x + Q + 1) - f (x + Q) = f (x + 1) - f x := by
        specialize g₁ x
        ring_nf at g₁ ⊢
        linarith only [g₁]
      have g₂ := lemma_1 (fun x => f (x + 1) - f x) T Q (by omega) (by omega)
      simp at g₂
      specialize g₂ g₀ g₁
      replace g₂ (x : ℤ) : f (x + 1 + T.gcd Q) - f (x + 1) = f (x + T.gcd Q) - f x := by
        specialize g₂ x
        ring_nf at g₂ ⊢
        linarith only [g₂]
      have g₂' := g₂
      replace g₂ (x : ℤ) (k : ℕ) : f (x + k + T.gcd Q) - f (x + k) = f (x + T.gcd Q) - f x := by
        induction k with
        | zero =>
          simp
        | succ k hk =>
          calc
            f (x + (k + 1) + T.gcd Q) - f (x + (k + 1)) = f (x + k + 1 + T.gcd Q) - f (x + k + 1) := by ring_nf
            _ = f (x + k + T.gcd Q) - f (x + k) := by apply g₂'
            _ = f (x + T.gcd Q) - f x := by apply hk
      clear g₂'
      replace g₂ (x k : ℤ) : f (x + k + T.gcd Q) - f (x + k) = f (x + T.gcd Q) - f x := by
        by_cases kpos : 0 ≤ k
        . specialize g₂ x k.natAbs
          simp [Int.natAbs_of_nonneg kpos] at g₂
          simp [g₂]
        . specialize g₂ (x + k) (-k).natAbs
          rw [Int.natAbs_of_nonneg (show 0 ≤ -k by omega)] at g₂
          ring_nf at g₂ ⊢
          linarith only [g₂]
      replace g₂ : T ≤ T.gcd Q := by
        apply hf₆'
        refine ⟨?_, ?_⟩
        . simp
          apply Nat.gcd_pos_of_pos_left
          omega
        . use f (T.gcd Q) - f 0
          intro x
          ring_nf
          specialize g₂ x (-x)
          ring_nf at g₂ ⊢
          exact g₂.symm
      replace g₂ : T = T.gcd Q := by
        apply le_antisymm
        . exact g₂
        . apply Int.le_of_dvd Tpos
          apply gcd_dvd_left
      simp at hT
      rw [even_iff_two_dvd] at hT
      absurd hQOdd
      simp
      rw [even_iff_two_dvd]
      zify
      calc
        (2 : ℤ) ∣ T := hT
        _ ∣ Q := by rw [g₂]; apply gcd_dvd_right
    -- Show that T ∣ f(x) for all x ∈ ℤ.
    have hf₈ : ∀ x : ℤ, T ∣ f x := by
      by_contra!
      obtain ⟨u, h₀⟩ := this
      -- There exists a odd prime p and a number α such that p ^ α ∣ T but p ^ α ∤ f(u).
      let T₀ := T.gcd (f u)
      let T₁ := T.natAbs
      let T₂ := max T₀ T₁ + 1
      have hT₀pos : T₀ > 0 := by
        apply Nat.gcd_pos_of_pos_right
        by_contra! hT₀
        replace hT₀ : f u = 0 := by
          omega
        absurd hOdd u
        simp [hT₀]
      have hT₀ := Nat.prod_pow_prime_padicValNat T₀ (by omega) T₂ (by omega)
      have hT₁ := Nat.prod_pow_prime_padicValNat T₁ (by omega) T₂ (by omega)
      have hT₂ : ∃ p α : ℕ, Nat.Prime p ∧ p ∈ Finset.range T₂ ∧ p ^ α ∣ T₁ ∧ ¬p ^ α ∣ T₀ := by
        by_contra hT₂
        push_neg at hT₂
        replace hT₂ : ∀ p α : ℕ, Nat.Prime p → p ∈ Finset.range T₂ → (α ≤ padicValNat p T₁ ↔ α ≤ padicValNat p T₀) := by
          intro p
          intro α
          intro h₀ h₁
          have h₀' := h₀
          rw [<-@fact_iff (Nat.Prime p)] at h₀'
          apply Iff.intro
          <;> intro h₂
          . replace h₂ : p ^ α ∣ T₁ := by
              rw [padicValNat_dvd_iff_le]
              exact h₂
              simp [T₁]
              omega
            specialize hT₂ p α h₀ h₁ h₂
            rw [padicValNat_dvd_iff_le] at hT₂
            exact hT₂
            omega
          . replace h₂ : p ^ α ∣ T₀ := by
              rw [padicValNat_dvd_iff_le]
              exact h₂
              simp [T₁]
              omega
            have h₃ : T₀ ∣ T₁ := by
              simp [T₀, T₁]
              apply Nat.gcd_dvd_left
            replace h₃ := h₂.trans h₃
            rw [padicValNat_dvd_iff_le] at h₃
            exact h₃
            omega
        replace hT₂ : ∀ p : ℕ, Nat.Prime p → p ∈ Finset.range T₂ → padicValNat p T₁ = padicValNat p T₀ := by
          intro p
          intro h₀
          intro h₁
          apply le_antisymm
          . specialize hT₂ p (padicValNat p T₁) h₀ h₁
            simp at hT₂
            exact hT₂
          . specialize hT₂ p (padicValNat p T₀) h₀ h₁
            simp at hT₂
            exact hT₂
        replace hT₂ : T₁ = T₀ := by
          calc
            T₁ = ∏ p ∈ Finset.filter (fun p ↦ Nat.Prime p) (Finset.range T₂), p ^ padicValNat p T₁ := hT₁.symm
            _ = ∏ p ∈ Finset.filter (fun p ↦ Nat.Prime p) (Finset.range T₂), p ^ padicValNat p T₀ := by
              rw [Finset.prod_congr]
              rfl
              intro p hp
              simp (config := { singlePass := true }) at hp
              congrm p ^ ?_
              . exact hT₂ p hp.2 hp.1
            _ = T₀ := hT₀
        absurd h₀
        rw [show T = T₁ by simp only [T₁, Int.natAbs_of_nonneg (le_of_lt Tpos)], hT₂]
        simp [T₀]
        apply gcd_dvd_right
      clear hT₀ hT₁
      obtain ⟨p, α, h₁, h₃, h₄, h₅⟩ := hT₂
      have h₂' : α ≠ 0 := by
        by_contra! h₂'
        rw [h₂'] at h₅
        simp at h₅
      have h₂ : Odd p := by
        by_contra h₂
        simp at h₂
        rw [Nat.Prime.even_iff h₁] at h₂
        absurd TOdd
        simp
        rw [even_iff_two_dvd]
        calc
          (2 : ℤ) ∣ p ^ α := by rw [h₂]; apply dvd_pow_self; exact h₂'
          _ ∣ (T₁ : ℤ) := by norm_cast
          _ = T := by simp only [T₁, Int.natAbs_of_nonneg (le_of_lt Tpos)]
      -- Substitute (x, y) = (u, 0) into the original equation, and see that p ^ α does not divide u + f(u) or u - f(u).
      have h₆ := hf₀ u 0
      simp at h₆
      replace h₆ : ∃ v : ℤ, |u - v| = |f u| ∧ ¬(p ^ α : ℤ) ∣ f v := by
        by_contra!
        have h₇ : (p ^ α : ℤ) ∣ 2 * f u := by
          calc
            (p ^ α : ℤ) ∣ f (u + f u) + f (u - f u) := by
              apply dvd_add
              . specialize this (u + f u)
                simp at this
                exact this
              . specialize this (u - f u)
                simp at this
                exact this
            _ = 2 * f u := by rw [h₆]; ring_nf
        apply Prime.left_dvd_or_dvd_right_of_dvd_mul at h₇
        cases h₇ with
        | inl weq =>
          norm_cast at weq
          apply Prime.dvd_of_dvd_pow at weq
          rw [<-even_iff_two_dvd] at weq
          absurd h₂
          simp [weq]
          rw [<-Nat.prime_iff]
          exact Nat.prime_two
        | inr h₇ =>
          absurd h₅
          simp [T₀, Int.gcd]
          rw [Nat.dvd_gcd_iff]
          refine ⟨h₄, ?_⟩
          zify
          simp [dvd_abs, h₇]
        exact Int.prime_two
      obtain ⟨v, h₆, h₇⟩ := h₆
      -- Set L = lcm(f(u), f(v)) and substitute (x, y) = (u, v) into hf₃.
      let L := (f u).lcm (f v)
      specialize hf₃ u v
      simp [show (f u).lcm (f v) = L by simp only [L]] at hf₃
      have hf₈' : 2 * (v - u) ≠ 0 := by
        by_contra! hf₈'
        simp at hf₈'
        rw [<-abs_neg] at h₆
        simp [hf₈'] at h₆
        symm at h₆
        rw [abs_eq_zero] at h₆
        absurd hOdd u
        simp [h₆]
      have hf₈ := lemma_1 (fun x => f (x + L) - f x) (2 * (v - u)) T hf₈' (by omega)
      simp at hf₈
      clear hf₈'
      have hf₈' (x : ℤ) : f (x + L + T) - f (x + L) = f (x + T) - f x := by
        rw [hf₇, hf₇]
      replace hf₈' (x : ℤ) : f (x + T + L) - f (x + T) = f (x + L) - f x := by
        specialize hf₈' x
        ring_nf at hf₈' ⊢
        linarith only [hf₈']
      replace hf₃ (x : ℤ) := (hf₃ x).symm
      specialize hf₈ hf₃ hf₈'
      -- Show that Δ_{gcd(2(v - u), T)} f is gcd(T, L)-periodic.
      have hf₉' : L ≠ 0 := by
        simp [L]
        apply Nat.lcm_ne_zero
        by_contra! hf₉'
        simp at hf₉'
        absurd hOdd u
        simp [hf₉']
        by_contra! hf₉'
        simp at hf₉'
        absurd hOdd v
        simp [hf₉']
      have hf₉ := lemma_1 (fun x => f (x + (2 * (v - u)).gcd T) - f x) T L (by omega) (by omega)
      simp at hf₉
      clear hf₉'
      have hf₉' (x : ℤ) : f (x + ((2 * (v - u)).gcd T) + T) - f (x + ((2 * (v - u)).gcd T)) = f (x + T) - f x := by
        rw [hf₇, hf₇]
      replace hf₉' (x : ℤ) : f (x + T + ((2 * (v - u)).gcd T)) - f (x + T) = f (x + ((2 * (v - u)).gcd T)) - f x := by
        specialize hf₉' x
        ring_nf at hf₉' ⊢
        linarith only [hf₉']
      replace hf₈ (x : ℤ) : f (x + ↑L + ((2 * (v - u)).gcd T)) - f (x + ↑L) = f (x + ((2 * (v - u)).gcd T)) - f x := by
        specialize hf₈ x
        ring_nf at hf₈ ⊢
        linarith only [hf₈]
      specialize hf₉ hf₉' hf₈
      have hT₀ : (p : ℤ) ∣ T := by
        calc
          (p : ℤ) ∣ p ^ α := by apply dvd_pow_self; exact h₂'
          _ ∣ (T₁ : ℤ) := by norm_cast
          _ = T := by simp only [T₁, Int.natAbs_of_nonneg (le_of_lt Tpos)]
      -- Show that gcd(2(v - u), T) divides T / p.
      have hT₁ : ↑((2 * (v - u)).gcd T) ∣ T / p := by
        rw [<-abs_neg, abs_eq_abs] at h₆
        simp at h₆
        suffices g : ↑((2 * f u).gcd T) ∣ T / p by
          cases h₆ with
          | inl h₆ =>
            rw [h₆]
            exact g
          | inr h₆  =>
            rw [h₆, mul_neg]
            simp
            exact g
        have h₈ : ¬p ^ α ∣ (2 * f u).gcd T := by
          intro h₈
          zify at h₈
          have h₉ : (p ^ α : ℤ) ∣ 2 * f u := h₈.trans (by apply gcd_dvd_left)
          apply Prime.left_dvd_or_dvd_right_of_dvd_mul at h₉
          cases h₉ with
          | inl h₉ =>
            norm_cast at h₉
            apply Prime.dvd_of_dvd_pow at h₉
            rw [<-even_iff_two_dvd] at h₉
            absurd h₂
            simp [h₉]
            rw [<-Nat.prime_iff]
            exact Nat.prime_two
          | inr h₉ =>
            absurd h₅
            zify
            simp [T₀, Int.gcd]
            norm_cast
            rw [Nat.dvd_gcd_iff]
            zify
            nth_rewrite 2 [dvd_abs]
            simp [T₁] at h₄
            zify at h₄
            exact ⟨h₄, h₉⟩
          exact Int.prime_two
        have h₉' : (2 * f u).gcd T ∣ T.natAbs := by
          zify
          rw [dvd_abs]
          apply gcd_dvd_right
        have h₉ : p ∣ T.natAbs / (2 * f u).gcd T := by
          apply dvd_of_one_le_padicValNat
          have h₁' := h₁
          rw [<-@fact_iff (Nat.Prime p)] at h₁'
          rw [padicValNat.div_of_dvd h₉']
          calc
            1 = α - (α - 1) := by rw [Nat.sub_sub_self (by omega)]
            _ ≤ padicValNat p T.natAbs - (α - 1) := by
              apply Nat.sub_le_sub_right
              rw [<-padicValNat_dvd_iff_le]
              simp [T₁] at h₄
              zify at h₄ ⊢
              exact h₄
              omega
            _ ≤ padicValNat p T.natAbs - padicValNat p ((2 * f u).gcd T) := by
              apply Nat.sub_le_sub_left
              contrapose! h₈
              apply Nat.add_one_le_of_lt at h₈
              rw [Nat.sub_add_cancel (by omega)] at h₈
              rw [<-padicValNat_dvd_iff_le] at h₈
              exact h₈
              simp [Int.gcd, -ne_eq]
              apply Nat.gcd_ne_zero_right
              omega
        zify at h₉
        rw [Int.dvd_div_iff_mul_dvd] at h₉ ⊢
        rw [mul_comm, dvd_abs] at h₉
        exact h₉
        exact hT₀
        zify at h₉'
        exact h₉'
      -- Show that gcd(L, T) divides T / p.
      have hT₂ : ↑((L : ℤ).gcd T) ∣ T / p := by
        replace h₇ : ¬(p ^ α : ℤ) ∣ L := by
          by_contra!
          simp [L, Int.lcm] at this
          norm_cast at this
          have h₁' := h₁
          rw [<-@fact_iff (Nat.Prime p)] at h₁'
          have h₈ := lemma_3 (f u).natAbs (f v).natAbs p (by simp; by_contra!; absurd hOdd u; simp [this]) (by simp; by_contra!; absurd hOdd v; simp [this])
          cases h₈ with
          | inl h₈ =>
            replace h₅ : ¬p ^ α ∣ (f u).natAbs := by
              contrapose! h₅
              simp [T₀, Int.gcd]
              rw [Nat.dvd_gcd_iff]
              simp [T₁] at h₄
              exact ⟨h₄, h₅⟩
            contrapose! h₅
            rw [padicValNat_dvd_iff_le, <-h₈, <-padicValNat_dvd_iff_le]
            exact this
            apply Nat.lcm_ne_zero
            . simp
              by_contra!
              absurd hOdd u
              simp [this]
            . simp
              by_contra!
              absurd hOdd v
              simp [this]
            . simp
              by_contra!
              absurd hOdd u
              simp [this]
          | inr h₈ =>
            contrapose! h₇
            rw [<-dvd_abs]
            rw [<-Int.natCast_natAbs]
            norm_cast
            rw [padicValNat_dvd_iff_le, <-h₈, <-padicValNat_dvd_iff_le]
            exact this
            apply Nat.lcm_ne_zero
            . simp
              by_contra!
              absurd hOdd u
              simp [this]
            . simp
              by_contra!
              absurd hOdd v
              simp [this]
            . simp
              by_contra!
              absurd hOdd v
              simp [this]
        have h₈ : ¬p ^ α ∣ (L : ℤ).gcd T := by
          intro h₈
          zify at h₈
          have h₉ : (p ^ α : ℤ) ∣ L := h₈.trans (by apply gcd_dvd_left)
          contradiction
        have h₉' : (L : ℤ).gcd T ∣ T.natAbs := by
          zify
          rw [dvd_abs]
          apply gcd_dvd_right
        have h₉ : p ∣ T.natAbs / (L : ℤ).gcd T := by
          apply dvd_of_one_le_padicValNat
          have h₁' := h₁
          rw [<-@fact_iff (Nat.Prime p)] at h₁'
          rw [padicValNat.div_of_dvd h₉']
          calc
            1 = α - (α - 1) := by rw [Nat.sub_sub_self (by omega)]
            _ ≤ padicValNat p T.natAbs - (α - 1) := by
              apply Nat.sub_le_sub_right
              rw [<-padicValNat_dvd_iff_le]
              simp [T₁] at h₄
              zify at h₄ ⊢
              exact h₄
              omega
            _ ≤ padicValNat p T.natAbs - padicValNat p ((L : ℤ).gcd T) := by
              apply Nat.sub_le_sub_left
              contrapose! h₈
              apply Nat.add_one_le_of_lt at h₈
              rw [Nat.sub_add_cancel (by omega)] at h₈
              rw [<-padicValNat_dvd_iff_le] at h₈
              exact h₈
              simp [Int.gcd, -ne_eq]
              apply Nat.gcd_ne_zero_right
              omega
        zify at h₉
        rw [Int.dvd_div_iff_mul_dvd] at h₉ ⊢
        rw [mul_comm, dvd_abs] at h₉
        exact h₉
        exact hT₀
        zify at h₉'
        exact h₉'
      rw [Int.gcd_comm] at hT₂
      -- Show that Δ_{T / p} Δ_{T / p} f = 0.
      replace hf₉ (x : ℤ) (k : ℕ) : f (x + k * (T.gcd L) + (2 * (v - u)).gcd T) - f (x + k * (T.gcd L)) = f (x + (2 * (v - u)).gcd T) - f x := by
        induction k with
        | zero =>
          simp
        | succ k hk =>
          calc
            f (x + (k + 1) * (T.gcd L) + (2 * (v - u)).gcd T) - f (x + (k + 1) * (T.gcd L)) = f (x + k * (T.gcd L) + T.gcd L + (2 * (v - u)).gcd T) - f (x + k * (T.gcd L) + T.gcd L) := by ring_nf
            _ = f (x + k * (T.gcd L) + (2 * (v - u)).gcd T) - f (x + k * (T.gcd L)) := by rw [hf₉]
            _ = f (x + (2 * (v - u)).gcd T) - f x := by rw [hk]
      replace hf₉ (x : ℤ) (k₁ k₂ : ℕ) : f (x + k₁ * (T.gcd L) + k₂ * ((2 * (v - u)).gcd T)) - f (x + k₁ * (T.gcd L)) = f (x + k₂ * ((2 * (v - u)).gcd T)) - f x := by
        induction k₂ generalizing x with
        | zero =>
          simp
        | succ k₂ hk₂ =>
          calc
            f (x + k₁ * (T.gcd L) + (k₂ + 1) * ((2 * (v - u)).gcd T)) - f (x + k₁ * (T.gcd L))
            _ = f (x + ((2 * (v - u)).gcd T) + k₁ * (T.gcd L) + k₂ * ((2 * (v - u)).gcd T)) - f (x + ((2 * (v - u)).gcd T) + k₁ * (T.gcd L)) + (f (x + k₁ * (T.gcd L) + ((2 * (v - u)).gcd T)) - f (x + k₁ * (T.gcd L))) := by ring_nf
            _ = f (x + ((2 * (v - u)).gcd T) + k₂ * ((2 * (v - u)).gcd T)) - f (x + ((2 * (v - u)).gcd T)) + (f (x + (2 * (v - u)).gcd T) - f x) := by rw [hk₂, hf₉]
            _ = f (x + (k₂ + 1) * ((2 * (v - u)).gcd T)) - f x := by ring_nf
      replace hf₉ (x k₁ k₂ : ℤ) : f (x + k₁ * (T.gcd L) + k₂ * ((2 * (v - u)).gcd T)) - f (x + k₁ * (T.gcd L)) = f (x + k₂ * ((2 * (v - u)).gcd T)) - f x := by
        by_cases hk₂ : 0 ≤ k₂
        . by_cases hk₁ : 0 ≤ k₁
          . specialize hf₉ x k₁.natAbs k₂.natAbs
            simp [Int.natAbs_of_nonneg hk₁, Int.natAbs_of_nonneg hk₂] at hf₉
            simp [hf₉]
          . specialize hf₉ (x + k₁ * (T.gcd L)) (-k₁).natAbs k₂.natAbs
            rw [Int.natAbs_of_nonneg (le_of_lt (by omega)), Int.natAbs_of_nonneg hk₂] at hf₉
            ring_nf at hf₉ ⊢
            linarith only [hf₉]
        . by_cases hk₁ : 0 ≤ k₁
          . specialize hf₉ (x + k₂ * ((2 * (v - u)).gcd T)) k₁.natAbs (-k₂).natAbs
            rw [Int.natAbs_of_nonneg hk₁, Int.natAbs_of_nonneg (le_of_lt (by omega))] at hf₉
            ring_nf at hf₉ ⊢
            linarith only [hf₉]
          . specialize hf₉ (x + k₁ * (T.gcd L) + k₂ * ((2 * (v - u)).gcd T)) (-k₁).natAbs (-k₂).natAbs
            rw [Int.natAbs_of_nonneg (le_of_lt (by omega)), Int.natAbs_of_nonneg (le_of_lt (by omega))] at hf₉
            ring_nf at hf₉ ⊢
            linarith only [hf₉]
      replace hf₉ (x : ℤ) := hf₉ x ((T / p) / (T.gcd L)) ((T / p) / ((2 * (v - u)).gcd T))
      replace hf₉ (x : ℤ) : f (x + T / p + T / p) - f (x + T / p) = f (x + T / p) - f x := by
        specialize hf₉ x
        rw [Int.ediv_mul_cancel, Int.ediv_mul_cancel] at hf₉
        exact hf₉
        assumption'
      have hf₁₀ (x : ℤ) : f (x + ↑((T.natAbs / p) * p) + 1) - f (x + ↑((T.natAbs / p) * p)) = f (x + 1) - f x := by
        norm_cast
        rw [show x + ↑((T.natAbs / p) * p) + 1 = x + 1 + ↑((T.natAbs / p) * p) by ac_rfl, Nat.div_mul_cancel, show T.natAbs = T by simp only [Int.natAbs_of_nonneg (le_of_lt Tpos)]]
        linarith only [hf₇ x, hf₇ (x + 1)]
        zify
        simp [dvd_abs, hT₀]
      have hf₁₂ : 0 < T.natAbs / p := by
        apply Nat.div_pos
        zify
        apply Int.le_of_dvd
        simp
        omega
        simp [dvd_abs]
        exact hT₀
        exact Nat.Prime.pos h₁
      -- Use lemma 2 to show that Δ_{T / p} Δ_1 f = 0.
      have hf₁₁ := lemma_2 (fun x => f (x + 1) - f x) p (T.natAbs / p) (Nat.Prime.pos h₁) hf₁₂
      simp at hf₁₁ hf₁₀
      specialize hf₁₁ hf₁₀
      rw [show |T| = T by simp only [abs_of_nonneg (le_of_lt Tpos)]] at hf₁₁
      have hf₁₁' (x : ℤ) : f (x + T / p + T / p + 1) - f (x + T / p + T / p) - (f (x + T / p + 1) - f (x + T / p)) = f (x + T / p + 1) - f (x + T / p) - (f (x + 1) - f x) := by
        calc
          f (x + T / p + T / p + 1) - f (x + T / p + T / p) - (f (x + T / p + 1) - f (x + T / p)) = f (x + 1 + T / p + T / p) - f (x + 1 + T / p) - (f (x + T / p + T / p) - f (x + T / p)) := by ring_nf
          _ = f (x + T / p + 1) - f (x + T / p) - (f (x + 1) - f x) := by rw [hf₉, hf₉]; ring_nf
      specialize hf₁₁ hf₁₁'
      clear hf₁₀ hf₁₁'
      -- A contradiction is derived from the fact that T / p is a smaller quasi-period of f.
      specialize hf₆' (T / p)
      replace hf₁₂ : T / p > 0 := by
        rw [show T = T.natAbs by simp only [Int.natAbs_of_nonneg (le_of_lt Tpos)]]
        norm_cast
      replace hf₁₁ (x : ℤ) (k : ℕ) : f (x + T / p + k) - f (x + k) = f (x + T / p) - f x := by
        induction k with
        | zero =>
          simp
        | succ k hk =>
          calc
            f (x + T / p + (k + 1)) - f (x + (k + 1)) = f (x + k + T / p + 1) - f (x + k + 1) := by ring_nf
            _ = f (x + k + T / p) - f (x + k) := by linarith only [hf₁₁ (x + k)]
            _ = f (x + T / p + k) - f (x + k) := by ac_rfl
            _ = f (x + T / p) - f x := by rw [hk]
      replace hf₁₁ (x k : ℤ) : f (x + T / p + k) - f (x + k) = f (x + T / p) - f x := by
        by_cases h : 0 ≤ k
        . specialize hf₁₁ x k.natAbs
          simp [Int.natAbs_of_nonneg h] at hf₁₁
          simp [hf₁₁]
        . specialize hf₁₁ (x + k) (-k).natAbs
          rw [Int.natAbs_of_nonneg (le_of_lt (by omega))] at hf₁₁
          ring_nf at hf₁₁ ⊢
          linarith only [hf₁₁]
      have hf₁₃ : ∃ G, ∀ (x : ℤ), f (x + T / ↑p) - f x = G := by
        use f (T / p) - f 0
        intro x
        specialize hf₁₁ x (-x)
        ring_nf at hf₁₁ ⊢
        linarith only [hf₁₁]
      specialize hf₆' ⟨hf₁₂, hf₁₃⟩
      rw [show T = T.natAbs by simp only [Int.natAbs_of_nonneg (le_of_lt Tpos)]] at hf₆'
      norm_cast at hf₆'
      apply Nat.eq_zero_of_le_div at hf₆'
      simp at hf₆'
      omega
      apply Nat.Prime.two_le h₁
    -- Show that G is even, and divisible by T, which is odd, so G = 2kT for some k ∈ ℤ.
    have hG₀ : Even G := by
      rw [<-hf₇ 0]
      apply Odd.sub_odd (hOdd (0 + T)) (hOdd 0)
    rw [even_iff_two_dvd] at hG₀
    have hG₁ : T ∣ G := by
      rw [<-hf₇ 0]
      apply dvd_sub (hf₈ (0 + T)) (hf₈ 0)
    have hG₂ : 2 * T ∣ G := by
      rw [<-Int.natAbs_dvd_natAbs] at hG₀ hG₁ ⊢
      rw [Int.natAbs_mul]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      simp
      simp [TOdd]
      assumption'
    rw [dvd_iff_exists_eq_mul_right] at hG₂
    obtain ⟨k, hG⟩ := hG₂
    clear hG₀ hG₁
    -- Show finally that f satisifies the given form.
    let l := @List.ofFn _ T.natAbs (fun n => f n / T)
    use T.natAbs, k, l
    zify
    simp [show |T| = T by simp only [abs_of_nonneg (le_of_lt Tpos)]]
    have hl : l.length = T := by
      simp [l]
      omega
    simp [hl]
    refine ⟨?_, ?_, ?_⟩
    . simp [TOdd]
    . intro l'
      by_contra!
      absurd hOdd l'
      simp at this ⊢
      rw [even_iff_two_dvd] at this ⊢
      calc
        2 ∣ f l' / T := this
        _ ∣ f l' := by rw [Int.div_dvd_iff_dvd_mul]; apply dvd_mul_left; exact hf₈ l'; omega
    . intro n
      have h₀ := @Int.emod_nonneg n T (by omega)
      have h₁ := @Int.emod_lt_of_pos n T Tpos
      have h₂ : (n % T).natAbs < T.natAbs := by
        zify
        simp [abs_of_nonneg h₀, abs_of_nonneg (le_of_lt Tpos), h₁]
      simp [l, h₂]
      simp [abs_of_nonneg h₀]
      rw [Int.ediv_mul_cancel, mul_comm, mul_assoc, <-mul_assoc, mul_comm T 2, <-mul_assoc, <-hG]
      by_cases nnonneg : 0 ≤ n
      . calc
          f n = f (T * (n / T) + n % T) := by rw [Int.ediv_add_emod]
          _ = ∑ i in Finset.range ((n / T).natAbs), (f (T * (i + 1) + n % T) - f (T * i + n % T)) + f (n % T) := by
            apply eq_add_of_sub_eq
            norm_cast
            rw [Finset.sum_range_sub (fun i => f (T * i + n % T)) (n / T).natAbs]
            zify
            rw [show |n / T| = n / T from abs_of_nonneg (by rw [<-ge_iff_le, Int.div_nonneg_iff_of_pos]; assumption')]
            simp
          _ = ∑ i in Finset.range ((n / T).natAbs), G + f (n % T) := by
            congrm ?_ + ?_
            . rw [Finset.sum_congr]
              . rfl
              . intro i hi
                rw [show T * (i + 1) + n % T = T * i + n % T + T by ring_nf, hf₇]
            . rfl
          _ = G * (n / T).natAbs + f (n % T) := by
            simp [Finset.sum_const, show |n / T| = n / T from abs_of_nonneg (by rw [<-ge_iff_le, Int.div_nonneg_iff_of_pos]; assumption'), show |n % T| = n % T from abs_of_nonneg h₀]
            rw [mul_comm]
          _ = G * (n / T) + f (n % T) := by
            zify
            simp [show |n / T| = n / T from abs_of_nonneg (by rw [<-ge_iff_le, Int.div_nonneg_iff_of_pos]; assumption')]
      . have h₃ : |n / T| = -(n / T) := by
          rw [<-abs_neg]
          simp [show n / T ≤ 0 from le_of_lt (by apply Int.ediv_neg' (by rw [not_le] at nnonneg; exact nnonneg); exact Tpos)]
        calc
          f n = f (T * (n / T) + n % T) := by rw [Int.ediv_add_emod]
          _ = -∑ i in Finset.range ((n / T).natAbs), (f (-T * i + n % T) - f (-T * (i + 1) + n % T)) + f (n % T) := by
            apply eq_add_of_sub_eq
            norm_cast
            rw [Finset.sum_range_sub' (fun i => f (-T * i + n % T)) (n / T).natAbs]
            zify
            rw [h₃]
            ring_nf
          _ = -∑ i in Finset.range ((n / T).natAbs), G + f (n % T) := by
            congrm ?_ + ?_
            . rw [Finset.sum_congr]
              . rfl
              . intro i hi
                ring_nf
                rw [show -(T * i) + n % T = -T - T * i + n % T + T by ring_nf, hf₇]
            . rfl
          _ = -G * (n / T).natAbs + f (n % T) := by
            rw [Finset.sum_const]
            simp
            rw [h₃]
            rw [mul_comm]
          _ = G * (n / T) + f (n % T) := by
            zify
            rw [h₃]
            ring_nf
      exact hf₈ (n % T)
  . -- Show that all such functions do satisfy the conditions.
    intro hf
    obtain ⟨d, k, l, hf₀, hf₁, hf₂, hf₃⟩ := hf
    refine ⟨?_, ?_⟩
    . -- Show that f(x) is odd for all x.
      intro x
      specialize hf₃ x
      have hf₄ : Even (2 * k * (x / ↑d) * ↑d) := by
        apply Even.mul_right
        apply Even.mul_right
        apply Even.mul_right
        norm_num
      have hf₅ : Odd (l[(x % ↑d).natAbs]! * ↑d) := by
        apply Odd.mul
        . apply hf₂
          rw [getElem!_pos]
          apply List.getElem_mem
          have g₀ := @Int.emod_nonneg x d (by by_contra!; absurd hf₀; norm_cast at this; simp [this])
          have g₁ := @Int.emod_lt_of_pos x d (by by_contra!; absurd hf₀; norm_cast at this; simp at this; simp [this])
          rw [hf₁]
          zify
          simp [show |x % ↑d| = x % ↑d by apply abs_of_nonneg g₀, g₁]
        . norm_cast
      rw [hf₃]
      apply Even.add_odd hf₄ hf₅
    . -- Show that f satisfies the functional equation.
      have hd (x : ℤ) : (d : ℤ) ∣ f x := by
        rw [hf₃, <-add_mul]
        apply dvd_mul_left
      have hf₄ (n : ℤ) (c : ℕ) : f (n + c * d) - f n = 2 * k * c * d := by
        rw [hf₃, hf₃]
        suffices g : (2 * k * ((n + ↑c * ↑d) / ↑d)) * ↑d - (2 * k * (n / ↑d)) * ↑d + (l[((n + ↑c * ↑d) % ↑d).natAbs]! * ↑d - l[(n % ↑d).natAbs]! * ↑d) = 2 * k * c * ↑d + 0 by
          linarith only [g]
        congrm ?_ + ?_
        . rw [<-sub_mul, <-mul_sub]
          simp
          left
          left
          rw [Int.add_mul_ediv_right, add_comm, Int.add_sub_cancel]
          by_contra!
          norm_cast at this
          rw [this] at hf₀
          absurd hf₀
          norm_num
        . rw [sub_eq_zero_of_eq]
          suffices g : ((n + ↑c * ↑d) % ↑d).natAbs = (n % ↑d).natAbs by
            rw [g]
          simp
      -- Show that Δ_{cd}f = 2kcd.
      have hf₄ (n c : ℤ) : f (n + c * d) - f n = 2 * k * c * d := by
        by_cases cnonneg : 0 ≤ c
        . specialize hf₄ n c.natAbs
          rw [show c.natAbs = c by simp [cnonneg]] at hf₄
          exact hf₄
        . replace cnonneg : 0 ≤ -c := by
            omega
          specialize hf₄ (n - (-c).natAbs * d) (-c).natAbs
          simp at hf₄
          rw [<-abs_neg, show |-c| = -c by apply abs_of_nonneg cnonneg] at hf₄
          simp at hf₄
          linarith only [hf₄]
      -- Finally show that f satisfies the functional equation.
      intro x y
      specialize hd x
      rw [dvd_iff_exists_eq_mul_left] at hd
      obtain ⟨c, hd⟩ := hd
      rw [hd]
      have hf₅ := hf₄ (x + y) c
      have hf₆ := hf₄ (x - y) (-c)
      ring_nf at hf₅ hf₆ ⊢
      linarith only [hf₅, hf₆]
