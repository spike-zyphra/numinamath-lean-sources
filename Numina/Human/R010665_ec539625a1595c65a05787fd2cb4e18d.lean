import Mathlib

/- When the expression $(2^1)(2^2)(2^3)\cdots (2^{99})(2^{100})$ is written as an integer,
what is the product of the tens digit and the ones digit? -/
theorem number_theory_19028{d_one d_ten: ℕ}
  (one_digit: d_one = (∏ i ∈ Finset.range 100, (2^(i + 1))) % 10)
  (ten_digit: d_ten = ((∏ i ∈ Finset.range 100, (2^(i + 1))) / 10) % 10):
  d_one * d_ten = 8 := by
  --let x i be 2^i mod 100
  let x:ℕ → ℕ
    | i => 2^i % 100
  have x_def(i:ℕ): x i = 2^i % 100 := rfl
  -- note that x i = x (20+i)
  have h1(i:ℕ): x (i+2) = x (22+i) := by
    rw [x_def (i+2), x_def (22+i)]
    have hh1: 2^(22+i) = 2^22 * 2^i := pow_add 2 22 i
    have hh2: 2^(i+2) = 4 * 2^i := by ring
    -- 2^5 =32, 2^10 = 1024, 2^20 mod 100 = ((2^10) mod 100)^2 = 24^2 mod 100 = 76
    -- 4x76=304, mod 100 = 4.
    rw [hh1, hh2]
    have hh3: 4 % 100 = 2^22 % 100 := by
      have tt1: 2^22 = 4 * ((2^10)*(2^10)) := by ring
      rw [tt1, Nat.mul_mod 4 _, Nat.mul_mod (2^10) _]
      have tt2: 2^10 % 100 = 24 := rfl
      have tt3: 24 * 24 % 100 = 76 := rfl
      rw [tt2, tt3]
    have hh4: 4 ≡ 2^22 [MOD 100] := by exact hh3
    have hh5: 4 * 2^i ≡ 2^22 * 2^i [MOD 100] := by
      apply Nat.ModEq.mul hh4 rfl 
    exact hh5
  -- 2^1x2^2x...x2^100 = 2^(1+2+...+100)
  have h2: (∏ i ∈ Finset.range 100, (2^(i + 1))) = 2^5050 := by
    have hh1(n:ℕ): (∏ i ∈ Finset.range n, (2^(i + 1))) =
      2 ^ (∑ i ∈ Finset.range n, (i+1)) := by
      induction' n with d hd
      · simp
      · rw [Finset.prod_range_succ, hd, Finset.sum_range_succ]
        ring
    rw [hh1 100]
    have hh2: ∑ i ∈ Finset.range 100, (i+1) = 5050 := by norm_num
    rw [hh2]
  -- notice that 5050 = 10 + 20 x 252, so 2^5050 mod 100 eq 2^5050 mod 10
  have h3: x 5050 = x 10 := by
    have hh1: 5050 = (8+2) + 20*252 := by ring
    have hh2(m n:ℕ): x ((m+2)+20*n) = x (m+2) := by
      induction' n with d hd
      · simp
      · have hh1: m+2+20*(d+1) = 22+(m+20*d) := by ring
        rw [hh1, ← h1, ← hd]
        congr 1
        ring
    rw [hh1, hh2]
  -- x 10 = 2^10 % 100 = 1024 % 100 = 24
  have h4: x 10 = 24 := by
    rw [x_def]; norm_num
  -- ones and tens digit of 2^5050 are those of x 10
  have h5(n:ℕ): n % 10 = (n % 100) % 10 := by
      have: 100 = 10*10 := by ring
      rw [this, Nat.mod_mul_left_mod]
  have hone: 2^5050 % 10 = (x 10) % 10 := by
    rw [h5 (2^5050), ← x_def, h3]
  have hten: (2^5050 / 10) % 10 = ((x 10) / 10) % 10 := by
    have(n:ℕ): (n / 10) % 10 = (n % 100) / 10 := by
      rw [← Nat.mod_mul_left_div_self]
    rw [this (2^5050), ← x_def, h3, h4]
  -- thus answer is 2x4=8
  rw [one_digit, ten_digit, h2, hone, hten, h4]