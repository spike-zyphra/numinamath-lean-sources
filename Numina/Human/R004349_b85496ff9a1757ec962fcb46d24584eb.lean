import Mathlib
open Nat Set
set_option maxHeartbeats 400000

-- Lean 4.15 lacks many GCD operation theorems, supplemented here as lemmas.
lemma Nat.gcd_eq_one_iff {m n : Nat} : Nat.gcd m n = 1 ↔ ∀ c, c ∣ m → c ∣ n → c = 1 := by
  simp [gcd_eq_iff]

lemma Nat.gcd_right_eq_iff {m n n' : Nat} : Nat.gcd m n = Nat.gcd m n' ↔ ∀ k, k ∣ m → (k ∣ n ↔ k ∣ n') := by
  refine ⟨fun h k hkm => ⟨fun hkn => ?_, fun hkn' => ?_⟩, fun h => Nat.dvd_antisymm ?_ ?_⟩
  · exact Nat.dvd_trans (h ▸ Nat.dvd_gcd hkm hkn) (Nat.gcd_dvd_right m n')
  · exact Nat.dvd_trans (h ▸ Nat.dvd_gcd hkm hkn') (Nat.gcd_dvd_right m n)
  · exact Nat.dvd_gcd_iff.2 ⟨Nat.gcd_dvd_left _ _, (h _ (Nat.gcd_dvd_left _ _)).1 (Nat.gcd_dvd_right _ _)⟩
  · exact Nat.dvd_gcd_iff.2 ⟨Nat.gcd_dvd_left _ _, (h _ (Nat.gcd_dvd_left _ _)).2 (Nat.gcd_dvd_right _ _)⟩

lemma Nat.dvd_mul_left_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ c * b :=
  Nat.dvd_trans h (Nat.dvd_mul_left _ _)

lemma Nat.gcd_mul_right_right_of_gcd_eq_one {n m k : Nat} : Nat.gcd n m = 1 → Nat.gcd n (m * k) = Nat.gcd n k := by
  rw [Nat.gcd_right_eq_iff, Nat.gcd_eq_one_iff]
  refine fun h l hl₁ => ⟨?_, fun a => Nat.dvd_mul_left_of_dvd a m⟩
  rw [Nat.dvd_mul]
  rintro ⟨k₁, k₂, hk₁, hk₂, rfl⟩
  obtain rfl : k₁ = 1 := h _ (Nat.dvd_trans (Nat.dvd_mul_right k₁ k₂) hl₁) hk₁
  simpa

lemma Nat.gcd_mul_left_right_of_gcd_eq_one {n m k : Nat} (h : gcd n m = 1) :
    gcd n (k * m) = gcd n k := by
  rw [Nat.mul_comm, gcd_mul_right_right_of_gcd_eq_one h]

lemma Nat.gcd_mul_right_left_of_gcd_eq_one {n m k : Nat} (h : gcd n m = 1) :
    gcd (n * k) m = gcd k m := by
  rw [gcd_comm, gcd_mul_right_right_of_gcd_eq_one (gcd_comm _ _ ▸ h), gcd_comm]

lemma Nat.gcd_mul_left_left_of_gcd_eq_one {n m k : Nat} (h : gcd n m = 1) :
    gcd (k * n) m = gcd k m := by
  rw [Nat.mul_comm, gcd_mul_right_left_of_gcd_eq_one h]

lemma Nat.gcd_pow_left_of_gcd_eq_one {k n m : Nat} (h : gcd n m = 1) : gcd (n ^ k) m = 1 := by
  induction k with
  | zero => simp [Nat.pow_zero]
  | succ k ih => rw [Nat.pow_succ, gcd_mul_left_left_of_gcd_eq_one h, ih]

lemma Nat.gcd_pow_right_of_gcd_eq_one {k n m : Nat} (h : gcd n m = 1) : gcd n (m ^ k) = 1 := by
  rw [gcd_comm, gcd_pow_left_of_gcd_eq_one (gcd_comm _ _ ▸ h)]

lemma Nat.pow_gcd_pow_of_gcd_eq_one {k l n m : Nat} (h : gcd n m = 1) : gcd (n ^ k) (m ^ l) = 1 :=
  gcd_pow_left_of_gcd_eq_one (gcd_pow_right_of_gcd_eq_one h)

lemma Nat.gcd_div_gcd_div_gcd_of_pos_left {n m : Nat} (h : 0 < n) :
    gcd (n / gcd n m) (m / gcd n m) = 1 := by
  rw [gcd_div (gcd_dvd_left _ _) (gcd_dvd_right _ _), Nat.div_self (gcd_pos_of_pos_left _ h)]

lemma Nat.pow_gcd_pow {k n m : Nat} : gcd (n ^ k) (m ^ k) = (gcd n m) ^ k := by
  refine (Nat.eq_zero_or_pos n).elim (by rintro rfl; cases k <;> simp [Nat.pow_zero]) (fun hn => ?_)
  conv => lhs; rw [← Nat.div_mul_cancel (gcd_dvd_left n m)]
  conv => lhs; arg 2; rw [← Nat.div_mul_cancel (gcd_dvd_right n m)]
  rw [Nat.mul_pow, Nat.mul_pow, gcd_mul_right, pow_gcd_pow_of_gcd_eq_one, Nat.one_mul]
  exact gcd_div_gcd_div_gcd_of_pos_left hn

-- Lemma: If the product of two coprime numbers is a square, then each is a square.
lemma h_sq_of_mul_eq_sq (a b c : ℕ) (h : a * b = c ^ 2) (hab : Nat.Coprime a b) : ∃ a0, a = a0 ^ 2 := by
  let d := Nat.gcd a c
  have h_d_square : d * d = Nat.gcd (a ^ 2) (c ^ 2) := by
    unfold d
    rw [Nat.pow_gcd_pow]
    simp [pow_two]
  have h_gcd_ab : Nat.gcd (a ^ 2) (c ^ 2) = Nat.gcd (a ^ 2) (a * b) := by
    rw [h]
  have h_gcd_a : Nat.gcd (a ^ 2) (a * b) = a := by
    rw [pow_two, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one, mul_one]
    exact hab
  have h_d_eq_a : d * d = a := by
    rw [h_d_square, h_gcd_ab, h_gcd_a]
  use d
  linarith

/-Example 7 Proof: The product of any three consecutive positive integers is not a perfect square.-/
theorem number_theory_60777 :
  ∀ x : ℕ, x > 0 → ¬∃ y : ℕ, x * (x + 1) * (x + 2) = y^2 := by
  -- Step $1$: Proof by contradiction, assume there exists x such that $x * (x + 1) * (x + 2)$ is a perfect square
  intro x h_x_pos h_contra
  rcases h_contra with ⟨y, h_y⟩
  have h_assumption : x * (x + 1) * (x + 2) = y^2 := h_y

  -- Step $2$: Prove pairwise coprimality.
  have h_coprime : Nat.gcd x (x + 1) = 1 ∧ Nat.gcd (x + 1) (x + 2) = 1 := by
    constructor
    · have : Nat.gcd x (x + 1) = Nat.gcd x 1 := by
        apply Nat.gcd_self_add_right x 1
      simp [this]
    · have : Nat.gcd (x + 1) (x + 1 + 1) = Nat.gcd (x + 1) 1 := by
        apply Nat.gcd_self_add_right (x + 1) 1
      simp [this]

  -- Step$ 3$: Case $1$, $x$ is odd.
  by_cases h_x_odd : Odd x
  · have h_coprime_odd : Nat.gcd x (x + 2) = 1 := by
      have : Nat.gcd x (x + 2) = Nat.gcd x 2 := by
        apply Nat.gcd_self_add_right x 2
      rw [this]
      have h₁: x % 2 = 1 := Nat.odd_iff.mp h_x_odd
      have h₂: ¬ 2 ∣ x := by omega
      have h₃: Nat.gcd 2 x = 1 := by
        have : (2).Coprime x := by
          have : @Prime 2 := by norm_num
          apply (Nat.Prime.coprime_iff_not_dvd this).mpr
          exact h₂
        have : IsCoprime (2 :ℤ)  x := by exact Nat.isCoprime_iff_coprime.mpr this
        exact Int.isCoprime_iff_gcd_eq_one.mp this
      rw [← h₃,gcd_comm]
    -- Establish all pairwise coprimality for $x, x + 1, x + 2$.
    have h_all_coprime : Nat.gcd x (x + 1) = 1 ∧ Nat.gcd x (x + 2) = 1 ∧ Nat.gcd (x + 1) (x + 2) = 1 := by
      constructor
      · exact h_coprime.1
      · constructor
        · exact h_coprime_odd
        · exact h_coprime.2
    -- Derive contradiction.
    have h_contradiction : False := by
      have h_coprime_x : Nat.gcd x ((x + 1) * (x + 2)) = 1 := by
        have : Nat.gcd x ((x + 1) * (x + 2)) = Nat.gcd x (x + 1)  := by
          exact Nat.gcd_mul_left_right_of_gcd_eq_one h_all_coprime.2.1
        rw [this]
        exact h_all_coprime.1
      have h_x_square : ∃ a, x = a^2 := by
        rw [mul_assoc] at h_assumption
        apply h_sq_of_mul_eq_sq x ((x + 1) * (x + 2)) y h_assumption h_coprime_x
      have h_x12_square : ∃ b, (x + 1) * (x + 2) = b^2 := by
        apply h_sq_of_mul_eq_sq ((x + 1) * (x + 2)) x y
        · rw [Nat.mul_comm, ← mul_assoc, h_assumption]
        · exact Nat.coprime_comm.mp h_coprime_x
      rcases h_x12_square with ⟨b, h_x12⟩
      -- Apply lemma to show $ (x + 1) * (x + 2)$ is a square.
      have h_not_square : ¬∃ k : ℕ, (x + 1) * (x + 2) = k^2 := by
        intro ⟨k, h_k⟩
        have h_lower : (x + 1) ^ 2 < (x + 1) * (x + 2) := by
          nlinarith
        have h_upper : (x + 1) * (x + 2) < (x + 2) ^ 2 := by
          nlinarith
        have h_bounds : (x + 1) ^ 2 < k ^ 2 ∧ k ^ 2 < (x + 2) ^ 2 := by omega
        have h_k_bounds : x + 1 < k ∧ k < x + 2 := by
          have : k > 0 := by nlinarith
          have : x + 1 > 0 := by linarith
          have : x + 2 > 0 := by linarith
          have h_sqrt_x1 : Nat.sqrt ((x + 1) ^ 2) = x + 1 := by rw [pow_two, Nat.sqrt_eq]
          have h_sqrt_x2 : Nat.sqrt ((x + 2) ^ 2) = x + 2 := by rw [pow_two, Nat.sqrt_eq]
          have h_sqrt_k : Nat.sqrt (k ^ 2) = k := by rw [pow_two, Nat.sqrt_eq]
          have h_lower_sqrt : Nat.sqrt ((x + 1) ^ 2) < k := by
            apply Nat.sqrt_lt.mpr
            rw [← pow_two k]
            exact h_bounds.1
          have h_upper_sqrt : Nat.sqrt (k ^ 2) < x + 2 := by
            apply Nat.sqrt_lt.mpr
            rw [← pow_two (x + 2)]
            exact h_bounds.2
          rw [h_sqrt_x1] at h_lower_sqrt
          rw [h_sqrt_k] at h_upper_sqrt
          exact ⟨h_lower_sqrt, h_upper_sqrt⟩
        have h_no_int : ¬∃ n : ℕ, x + 1 < n ∧ n < x + 2 := by
          intro ⟨n, h_n⟩
          have : n ≤ x + 1 := Nat.le_of_lt_succ h_n.2
          have : x + 1 < n := h_n.1
          linarith
        linarith
      have : ∃ k : ℕ, (x + 1) * (x + 2) = k^2 := by
        use b
      contradiction
    contradiction

  -- Step $4$: Case$ 2$, $x$ is even.
  · have h_x_even : Even x := by
      exact Nat.not_odd_iff_even.mp h_x_odd
    have h₁: x % 2 = 0 := Nat.even_iff.mp h_x_even
    have h₂: 2 ∣ x := by omega
    have h_gcd_2 : Nat.gcd x (x + 2) = 2 := by
      have : Nat.gcd x (x + 2) = Nat.gcd x 2 := by
        apply Nat.gcd_self_add_right x 2
      rw [this]
      have h₃: Nat.gcd 2 x = 2 := by
        exact Nat.gcd_eq_left_iff_dvd.mp h₂
      rw [gcd_comm]
      exact h₃
    let k := x / 2
    have h_x_2k : x = 2 * k := by omega
    have h_k_pos : k > 0 := by omega
    -- Derive $k * (x + 1) * (k + 1) = (y / 2) ^ 2$.
    have h_prod : k * (x + 1) * (k + 1) = (y / 2) ^ 2 := by
      rw [h_x_2k] at h_assumption
      have : x + 1 = 2 * k + 1 := by rw [h_x_2k]
      rw [← this] at h_assumption
      have : 2 * k + 2 = 2 * (k + 1) := by omega
      rw [this, ← mul_assoc] at h_assumption
      have h_sq_4: 4 ∣ y^2 := by
        use k * (x + 1) * (k + 1)
        rw [← h_assumption]
        ring
      have h_y_even : 2 ∣ y := by
        have : 4 = 2 ^ 2 := by norm_num
        rw [this] at h_sq_4
        have : 2 ∣ y^2 := by
          exact Nat.dvd_of_pow_dvd (by nlinarith) h_sq_4
        have : Even (y ^ 2) := even_iff_two_dvd.mpr this
        have : Even y := by exact (Nat.even_pow' (by norm_num: 2 ≠ 0)).mp this
        have : 2 ∣ y := even_iff_two_dvd.mp this
        exact this
      have : y^2 = (y / 2 * 2)^2 := by
        have : y / 2 * 2 = y := Nat.div_mul_cancel h_y_even
        rw [← this]
        simp
      rw [this] at h_assumption
      have h₁: (y / 2 * 2) ^ 2 = (y / 2)^2 * 2^2 := by exact Nat.mul_pow (y / 2) 2 2
      have h₂: 2 * k * (x + 1) * 2 * (k + 1) =  k * (x + 1) * (k + 1) * 4 := by ring
      have h₃: 2^2 = 4 := by norm_num
      rw [h₁,h₃,h₂] at h_assumption
      have : k * (x + 1) * (k + 1) = (y / 2) ^ 2 := by linarith
      exact this
    -- Establish pairwise coprimality for $k, x + 1, k + 1$.
    have h_all_coprime : Nat.gcd k (x + 1) = 1 ∧ Nat.gcd (x + 1) (k + 1) = 1 := by
      constructor
      · have : Nat.gcd (x + 1) k ∣ Nat.gcd (x + 1) x := by
          apply Nat.gcd_dvd_gcd_of_dvd_right
          rw [h_x_2k]
          simp
        have : Nat.gcd (x + 1) k = 1 := by
          apply Nat.eq_one_of_dvd_one
          have h_coprime' : (x + 1).gcd x = 1 := by rw [Nat.gcd_comm] ;exact h_coprime.1
          exact Nat.dvd_trans this (Nat.dvd_one.mpr h_coprime')
        rw [Nat.gcd_comm]
        exact this
      · have : Nat.gcd (x + 1) (k + 1) ∣ Nat.gcd (x + 1) (x + 2) := by
          apply Nat.gcd_dvd_gcd_of_dvd_right
          have : k + 1 = (x + 2) / 2 := by omega
          rw [this]
          have h₂': 2 ∣ (x + 2) := by omega
          exact Nat.div_dvd_of_dvd h₂'
        have : Nat.gcd (x + 1) (k + 1) = 1 := by
          apply Nat.eq_one_of_dvd_one
          exact Nat.dvd_trans this (Nat.dvd_one.mpr h_coprime.2)
        exact this
    have h_coprime_k : Nat.gcd (x + 1) (k * (k + 1)) = 1 := by
      have : Nat.gcd (x + 1) (k * (k + 1)) = Nat.gcd (x + 1) k  := by
        exact Nat.gcd_mul_left_right_of_gcd_eq_one h_all_coprime.2
      rw [this, Nat.gcd_comm]
      exact h_all_coprime.1
    have h_x12_square : ∃ b, k * (k + 1) = b^2 := by
      have : (x + 1) * (k * (k + 1)) = (y / 2) ^ 2 := by
        rw [mul_comm k (x + 1), mul_assoc] at h_prod
        exact h_prod
      apply h_sq_of_mul_eq_sq (k * (k + 1)) (x + 1) (y / 2)
      · rw [Nat.mul_comm, this]
      · exact Nat.coprime_comm.mp h_coprime_k
    rcases h_x12_square with ⟨b, h_x12⟩
    -- Apply lemma to show $k * (k + 1)$ is a square.
    have h_not_square : ¬∃ m : ℕ, k * (k + 1) = m^2 := by
      intro ⟨m, h_m⟩
      have h_lower : k ^ 2 < k * (k + 1) := by nlinarith
      have h_upper : k * (k + 1) < (k + 1) ^ 2 := by nlinarith
      have h_bounds : k ^ 2 < m ^ 2 ∧ m ^ 2 < (k + 1) ^ 2 := by omega
      have h_m_bounds : k < m ∧ m < k + 1 := by
        have : m > 0 := by nlinarith
        have : k > 0 := h_k_pos
        have : k + 1 > 0 := by linarith
        have h_sqrt_k : Nat.sqrt (k ^ 2) = k := by
          rw [pow_two,Nat.sqrt_eq]
        have h_sqrt_k1 : Nat.sqrt ((k + 1) ^ 2) = k + 1 := by
          rw [pow_two,Nat.sqrt_eq]
        have h_sqrt_m : Nat.sqrt (m ^ 2) = m := by
          rw [pow_two,Nat.sqrt_eq]
        have h_lower_sqrt : Nat.sqrt (k ^ 2) < m := by
          apply Nat.sqrt_lt.mpr
          rw [← pow_two m]
          exact h_bounds.1
        have h_upper_sqrt : Nat.sqrt (m ^ 2) < k + 1 := by
          apply Nat.sqrt_lt.mpr
          rw [← pow_two (k + 1)]
          exact h_bounds.2
        rw [h_sqrt_k] at h_lower_sqrt
        rw [h_sqrt_m] at h_upper_sqrt
        exact ⟨h_lower_sqrt, h_upper_sqrt⟩
      have h_no_int : ¬∃ n : ℕ, k < n ∧ n < k + 1 := by
        intro ⟨n, h_n⟩
        have : n ≤ k := Nat.le_of_lt_succ h_n.2
        have : k < n := h_n.1
        linarith
      linarith
    -- Construct contradiction: h_x12_square asserts $k * (k + 1)$ is a square.
    have : ∃ m : ℕ, k * (k + 1) = m^2 := by
      use b
    contradiction
