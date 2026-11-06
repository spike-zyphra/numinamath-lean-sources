import Mathlib

/-- `f m` is the unit digit of `m`. -/
def f (m : ℕ) : ℕ := m % 10

/-- `a n` is the unit digit of `2^(n+1) - 1`. -/
def a (n : ℕ) : ℕ := f (2^(n+1) - 1)

lemma two_pow_mod_ten_sub_one {k : ℕ} (hk : 1 ≤ k) (hmod : 2 ^ k % 10 = 6) :
    (2 ^ k - 1) % 10 = 5 := by
  -- Since 2^k ≡ 6 (mod 10) and 2^k ≥ 2^1 = 2, we have 2^k - 1 ≡ 5 (mod 10)
  have h2k : 2 ^ k ≥ 2 := by 
    refine Nat.le_self_pow ?_ 2
    omega
  calc
      _ = (2 ^ k - 1 + 10) % 10 := by omega
      _ = (2 ^ k + 9) % 10 := by omega
      _ = (2 ^ k % 10 + 9) % 10 := by rw [Nat.add_mod]
      _ = (6 + 9) % 10 := by rw [hmod]
      _ = 15 % 10 := by rfl
      _ = 5 := by norm_num

lemma six_pow_mod_ten {q : ℕ} (h : q ≥ 1) : 6 ^ q % 10 = 6 := by
  induction q with
  | zero => omega
  | succ q ih =>
    cases q with
    | zero => simp
    | succ =>
      rw [pow_succ, Nat.mul_mod]
      rw [ih (by omega)]

/-
We show that for any natural number `k ≥ 1`, the unit digit of `2^k` follows the cycle
```
2, 4, 8, 6
```
in other words:
```lean
2^k % 10 = match k % 4 with
| 1 => 2
| 2 => 4
| 3 => 8
| _ => 6
```
-/
lemma pow_two_mod10_cycle {k : ℕ} (hk : 1 ≤ k) :
  2 ^ k % 10 =
    match k % 4 with
    | 1 => 2
    | 2 => 4
    | 3 => 8
    | _ => 6 := by
  -- Write k = 4 * (k / 4) + (k % 4)
  let q := k / 4
  let r := k % 4
  have hkr : k = 4 * q + r := by
    -- `div_add_mod`: k = (k / 4) * 4 + k % 4
    simpa [mul_comm] using (Nat.div_add_mod k 4).symm

  -- case A: q = 0, case B: q ≥ 1, split on q
  by_cases hq : q = 0

  -- case A: q = 0
  . have: k < 4 := by
      calc
        k = 4 * q + r := by rw [hkr]
        _ = 4 * 0 + r := by simp [hq]
        _ = r := by simp
        _ < 4 := Nat.mod_lt _ (by norm_num)
    -- we only have finite cases for k = 1, 2, 3, prove by cases
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    cases hk_cases with
    | inl h => simp [h]
    | inr h => cases h with
      | inl h => simp [h]
      | inr h => simp [h]


  . -- case B: q ≥ 1
    have hq : 1 ≤ q := by omega

    -- Compute 2^k % 10
    calc
      2 ^ k % 10 = 2 ^ (4 * q + r) % 10 := by rw [hkr]
      _ = (2 ^ (4 * q) * 2 ^ r) % 10 := by simp [pow_add]
      _ = ((2 ^ 4) ^ q * 2 ^ r) % 10 := by simp [pow_mul]
      _ = (16 ^ q * 2 ^ r) % 10 := rfl
      -- since 16 ≡ 6 mod 10, we have 16^q ≡ 6^q mod 10
      _ = (6 ^ q * 2 ^ r) % 10 := by
        have : 16 % 10 = 6 := by rfl
        show (16 ^ q * 2 ^ r) % 10 = (6 ^ q * 2 ^ r) % 10
        calc
          _ = ((10 + 6) ^ q * 2 ^ r) % 10 := by norm_num
          _ = (6 ^ q * 2 ^ r) % 10 := by simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod]
      _ = (6 * 2 ^ r) % 10 := by
        -- for any q ≥ 1, 6^q % 10 = 6
        have : 6 ^ q % 10 = 6 := six_pow_mod_ten hq
        simp [Nat.mul_mod, this]

    -- Now we finish by showing (6 * 2^r) % 10 equals the cycle value
    have hr : r < 4 := Nat.mod_lt _ (by norm_num)
    rw [(by rfl: r = k % 4)]
    cases h : k % 4 with
    | zero => norm_num
    | succ n =>
      cases n with
      | zero => norm_num
      | succ n =>
        cases n with
        | zero => norm_num
        | succ n =>
          cases n with
          | zero => norm_num
          | succ => have : k % 4 < 4 := Nat.mod_lt _ (by norm_num); omega



/-- For any `N`, `a N` equals
```
1 if (N+1) % 4 = 1,
3 if (N+1) % 4 = 2,
7 if (N+1) % 4 = 3,
5 if (N+1) % 4 = 0.
```
-/
theorem aN_cycle (N : ℕ) :
  a N = if (N+1) % 4 = 1 then 1
        else if (N+1) % 4 = 2 then 3
        else if (N+1) % 4 = 3 then 7
        else 5 := by
  let k := N + 1
  have hk_ge_1 : 1 ≤ k := by omega
  have h2k : 2 ^ k ≥ 2 := by 
    refine Nat.le_self_pow ?_ 2
    omega
  -- We perform a case split on `k % 4`, which by definition is in `0, 1, 2, 3`.
  cases h0 : k % 4 with
  | zero =>
    -- Case `(N+1) % 4 = 0`: then `2^k % 10 = 6` and so `(2^k - 1) % 10 = 5`.
    dsimp [a, f]
    have h2 : (2 ^ k) % 10 = 6 := by
      -- `2^k % 10 = (2 % 10) ^ k % 10`, and since `k % 4 = 0`, the cycle gives `6`.
      have : (2 : ℕ) % 10 = 2 := by norm_num
      calc
        (2 ^ k) % 10 = (2 % 10) ^ k % 10 := by simp [Nat.pow_mod]
        _ = 2 ^ k % 10         := by rw [this]
        _ = 6                  := by
          -- because `k % 4 = 0`, `2^k % 10` is `6` in the 2-4-8-6 cycle
          rw [pow_two_mod10_cycle hk_ge_1]
          simp [h0]
    have h3: (2 ^ k - 1) % 10 = 5 := by
      calc
          _ = (2 ^ k - 1 + 10) % 10 := by omega
          _ = (2 ^ k + 9) % 10 := by omega
          _ = (2 ^ k % 10 + 9) % 10 := by rw [Nat.add_mod]
          _ = (6 + 9) % 10 := by rw [h2]
          _ = 15 % 10 := by rfl
          _ = 5 := by norm_num
    rw [h3]
  | succ n' =>
    cases n' with
    | zero =>
      -- Case `(N+1) % 4 = 1`: `2^k % 10 = 2`, so `(2^k - 1)%10 = 1`.
      dsimp [a, f]
      have : (2 ^ k - 1) % 10 = 1 := by
        have h2 : (2 ^ k) % 10 = 2 := by
          have : k % 4 = 1 := by rw [h0]
          calc
            (2 ^ k) % 10 = (2 % 10) ^ k % 10 := by simp [Nat.pow_mod]
            _ = 2 ^ k % 10                  := by norm_num
            _ = 2                          := by
              rw [pow_two_mod10_cycle hk_ge_1]
              simp [h0]

        calc
          _ = (2 ^ k - 1 + 10) % 10 := by omega
          _ = (2 ^ k + 9) % 10 := by omega
          _ = (2 ^ k % 10 + 9) % 10 := by rw [Nat.add_mod]
          _ = (2 + 9) % 10 := by rw [h2]
          _ = 11 % 10 := by rfl
          _ = 1 := by norm_num

      rw [this]

    | succ n'' =>
      cases n'' with
      | zero =>
        -- Case `(N+1) % 4 = 2`: `2^k % 10 = 4`, so `(2^k - 1)%10 = 3`.
        dsimp [a, f]
        have : (2 ^ k - 1) % 10 = 3 := by
          have h2 : (2 ^ k) % 10 = 4 := by
            rw [pow_two_mod10_cycle hk_ge_1]
            simp [h0]
          calc
            (2 ^ k - 1) % 10 = (2 ^ k - 1 + 10) % 10 := by omega
                           _ = (2 ^ k + 9) % 10 := by omega
                           _ = (2 ^ k % 10 + 9) % 10 := by rw [Nat.add_mod]
                           _ = (4 + 9) % 10 := by rw [h2]
                           _ = 13 % 10 := by rfl
                           _ = 3 := by norm_num
        rw [this]

      | succ n''' =>
        cases n''' with
        | zero =>
          -- Case `(N+1) % 4 = 3`: `2^k % 10 = 8`, so `(2^k - 1)%10 = 7`.
          dsimp [a, f]
          have : (2 ^ k - 1) % 10 = 7 := by
            have h2 : (2 ^ k) % 10 = 8 := by
              rw [pow_two_mod10_cycle hk_ge_1]
              simp [h0]
            calc
              (2 ^ k - 1) % 10 = (2 ^ k - 1 + 10) % 10 := by omega
              _ = (2 ^ k + 9) % 10 := by omega
              _ = (2 ^ k % 10 + 9) % 10 := by rw [Nat.add_mod]
              _ = (8 + 9) % 10 := by rw [h2]
              _ = 17 % 10 := by rfl
              _ = 7 := by norm_num
          rw [this]
        | succ _ =>
          -- This case is impossible because `k % 4 < 4`.
          have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
          omega
