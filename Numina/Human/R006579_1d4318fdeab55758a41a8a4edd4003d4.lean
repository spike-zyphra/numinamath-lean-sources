import Mathlib

open Nat

/--
  `N k` is the decimal number "120", then k copies of "3", then "08".
  Equivalently,
    N k = 120·10^(k+2) + 300·∑ i in Finset.range k, 10^i + 8.
  For k=0 this is 12008; for k=1 it is 120308; etc.

  If `m > 0`, `gcd m 9 = 1`, and `m` divides both 108300 and 228,
  then in fact for **every** `k` we have `m ∣ N k`.
-/
theorem divides_all_N
  {m : ℕ}
  (h_pos  : 0 < m)
  (h_gcd  : Nat.gcd m 9 = 1)
  (h108   : m ∣ 108300)
  (h228   : m ∣ 228)
  : ∀ k, m ∣ 8 + 300 * (∑ i ∈ Finset.range k, 10 ^ i) + 120 * 10 ^ (k + 2) := by

  let N := fun k => 8 + 100 * (10 ^ k - 1) / 3+ 120 * 10 ^ (k + 2)

  have geo_sum: ∀ k, (∑ i ∈ Finset.range k, 10 ^ i) = (10 ^ k - 1) / 9 := by
    intro k
    rw [geomSum_eq]
    omega

  have h_9_div: ∀ k, 9 ∣ 10 ^ k - 1 := by
    intro k
    calc
      _ = 10 - 1 := by omega
      _ ∣ 10 ^ k - 1 ^ k := by apply nat_sub_dvd_pow_sub_pow
      _ = 10 ^ k - 1 := by simp

  have h_N: ∀ k, 8 + 100 * (10 ^ k - 1) / 3+ 120 * 10 ^ (k + 2) = 8 + 300 * (∑ i ∈ Finset.range k, 10 ^ i) + 120 * 10 ^ (k + 2) := by
    intro k
    rw [geo_sum]
    congr
    have: 9 ∣ 10 ^ k - 1 := h_9_div k
    omega


  -- First, from gcd m 9 = 1 we get gcd m 3 = 1
  have hg3 : Nat.gcd m 3 = 1 := by
    -- gcd m 3 divides m and 3, hence also divides 9
    have d₁ :  Nat.gcd m 3 ∣ m      := Nat.gcd_dvd_left _ _
    have d₂ : Nat.gcd m 3 ∣ (3 : ℕ) := Nat.gcd_dvd_right _ _
    have d₃ : (3 : ℕ) ∣ 9      := ⟨3, by norm_num⟩
    -- have d₄ : Nat.gcd m 3 ∣ 9      := dvd_trans d₂ d₃
    -- have d₅ : Nat.gcd m 3 ∣ Nat.gcd m 9 := Nat.dvd_gcd d₁ d₄
    -- but gcd m 9 = 1
    exact Coprime.coprime_dvd_right d₃ h_gcd
  -- hence m is coprime to 3
  have cop3 : Coprime m 3 := by
    simpa [coprime_iff_gcd_eq_one] using hg3

  -- from m ∣ 228 = 3 * 76 and coprime to 3, we get m ∣ 76
  have d76 : m ∣ 76 := by
    have : m ∣ 3 * 76 := by simpa [mul_comm] using h228
    exact cop3.dvd_of_dvd_mul_left this

  -- and 76 * 158 = 12008 = N 0, so m ∣ N 0
  have dN0 : m ∣ N 0 := by
    have : m ∣ 76 * 158 := dvd_mul_of_dvd_left d76 _
    simpa [N] using this

  -- Now strong induction on k
  intro k
  rw [← (h_N k)]
  have ind : ∀ n, (∀ t < n, m ∣ N t) → m ∣ N n := by
    intro n ih
    cases n with
    | zero   => exact dN0
    | succ n =>
      -- inductive hypothesis: m ∣ N n
      have dNk : m ∣ N n := ih n (by simp)
      -- compute N (n+1) - N n = 108300 * 10^n

      -- N (n+1) = 120*10^(n+3) + 300*∑ i< n+1,10^i + 8
        -- N n       = 120*10^(n+2) + 300*∑ i< n,   10^i + 8
        -- subtracting gives 120·9·10^(n+2) + 300·10^n = 108300·10^n

      have h₃ : 10 ^ (n + 3) = 10 ^ n * 1000 := by simp [pow_add]
      have h₄ : 10 ^ (n + 2) = 10 ^ n * 100 := by simp [pow_add]
      have h₅ : 10 ^ (n + 1) = 10 ^ n * 10 := by simp [pow_add]
      have h₆ : 8 + 100 * (10 ^ n - 1) / 3 + 120 * (10 ^ n * 100) = 8 + (100 * (10 ^ n - 1) / 3 + 120 * (10 ^ n * 100)) := by ring
      have h₇ : 120 * (10 ^ n * 1000) - 120 * (10 ^ n * 100) = 108000 * 10 ^ n := by
        calc _ = 120 * 1000 * 10 ^ n  - 120 * 100* 10 ^ n := by ring_nf
              _ = 120000 * 10 ^ n - 12000 * 10 ^ n := by norm_num
              _ = (120000 - 12000) * 10 ^ n := by rw [← tsub_mul]
              _ = 108000 * 10 ^ n := by norm_num

      -- show that 3 divides 10^n * 10 - 1 by using the fact that 3 divides 10 - 1
      have h₈ : 3 ∣ 10 ^ n * 10 - 1:= by
        calc
          _ ∣ 10 - 1 := by omega
          _ ∣ 10 ^ (n+1) - 1:= by apply h_9_div
          _ = 10 ^ n * 10 - 1 := by omega

      -- show that 3 divides 10^n - 1 by using the fact that 3 divides 10 - 1
      have h₉ : 3 ∣ 10 ^ n - 1 := by
        calc
          _ ∣ 10 - 1 := by omega
          _ ∣ 10 ^ n - 1:= by apply h_9_div

      -- show that 3 divides 100 * (10 ^ n * 10 - 1) / 3 - 100 * (10 ^ n - 1) / 3
      have h_sub_div : 100 * (10 ^ n * 10 - 1) / 3 - 100 * (10 ^ n - 1) / 3  = 300 * 10^n := by omega

      -- show that N (n+1) - N n = 108300 * 10^n by simplifying the difference
      have h_diff : N (n+1) - N n = 108300 * 10^n := by
        calc
          N (n+1) - N n
              = (8 + 100 * (10 ^ (n+1) - 1) / 3+ 120 * 10 ^ (n + 1 + 2))
                - (8 + 100 * (10 ^ n - 1) / 3+ 120 * 10 ^ (n + 2)) := by
                  dsimp [N]

            _ = 100 * (10 ^ n * 10 - 1) / 3 + 120 * (10 ^ n * 1000) - (100 * (10 ^ n - 1) / 3 + 120 * (10 ^ n * 100)) := by
                  simp_rw [h₃, h₄, h₅]
                  rw [add_assoc]
                  rw [h₆]
                  rw [tsub_add_eq_tsub_tsub]
                  rw [add_comm]
                  rw [<-tsub_tsub_eq_add_tsub_of_le (by omega)]
                  norm_num

            _ = 108300 * 10^n := by omega

      -- show that m divides N (n+1) - N n by multiplying 108300 by 10^n
      have dDiff : m ∣ (N (n+1) - N n) := by
        calc
          m ∣ 108300 := h108
          _ ∣ 108300 * 10^n := by omega
          _ = N (n+1) - N n := by rw [h_diff]

      -- to use omega simplify N n + (N (n+1) - N n), we need to show that 10^n > 0
      have : 10^n > 0 := by
          exact pos_of_neZero (10 ^ n)

      -- simplify N (n+1) = N n + (N (n+1) - N n)
      have h_add : N (n+1) = N n + (N (n+1) - N n) := by
        omega

      -- show that m divides N n + (N (n+1) - N n) by adding the two divisibilities
      have h_dvd_diff : m ∣ N n + (N (n + 1) - N n):= Nat.dvd_add dNk dDiff

      rw [←h_add] at h_dvd_diff
      exact h_dvd_diff

  -- apply strong induction on n
  have divides_all_N :
    ∀ n, m ∣ N n := by
    intro n
    -- instantiate the `p : ℕ → Prop` to be `fun k => m ∣ N k` and apply strong induction at `n`
    apply @Nat.strong_induction_on (fun k => m ∣ N k) n ind

  have: m ∣ N k:= by apply divides_all_N
  dsimp [N] at this
  exact this
