import Mathlib

open BigOperators Finset Nat


-- Number_Theory_635408

/- Let $k$ be an odd positive integer such that $(k+1)/2$ is congruent to $1 \pmod 5$ and $k$
is congruent to $1 \pmod 6$. Let $N$ be the largest positive integer that can be expressed
as a $k$-digit base-(-4) number. The digits allowed are $\{0, 1, 2, 3\}$. Show that the remainder
when $N$ is divided by 210 is 3. -/

-- define digit d n, in order to let N be the largest positive integer that can be expressed
-- as a k-digit base-(-4) number, the digit d n should be 3 if n is even, and 0 if n is odd.

set_option linter.unusedVariables false

def d (n : ℕ) : ℕ :=
  if Even n then 3 else 0


-- prove that if number ends with 6, then (16 ^ (a + 1) - 1) % 5 = 0
@[simp]
lemma d0_digit6_dvd_5 (a : ℕ) : (16 ^ (a + 1) - 1) % 5 = 0 := by
  induction' a with d hd
  .
    -- base case
    group
  .
    -- inductive step
    have h1 : (16 ^ (d + 1 + 1) - 1) = (16 ^ (d + 1) - 1) + 16 ^ (d + 1) * 15 := by
      omega
    rw [h1]
    omega


-- prove (4 ^ (30 * a + 2) - 1) / 5 % 210 = 3, use induction
@[simp]
lemma N_mod_210 (a : ℕ) : (16 ^ (15 * a + 1) - 1) / 5 % 210 = 3 := by

  -- have h1 : (16 ^ (15 * a + 1) - 1) % 5 = 0 := by simp

  induction' a with d hd
  .
    -- base case
    group
  .
    -- inductive step
    have h1 : 16 ^ (15 * d) * 16 * (16 ^ 15 - 1) / 5 % 210 = 0 := by
      omega

    -- three part are integers
    have h2 : (16 ^ (15 * d + 15 + 1) - 1) % 5 = 0 := by simp
    have h3 : (16 ^ (15 * d + 1) - 1) % 5 = 0 := by simp
    have h4 : 16 * (16 ^ 15 - 1) % 5 = 0 := by group

    -- prove equation both sides not divisible by 5
    have h5 : 16 ^ (15 * d + 1 + 15) - 1 = 16 ^ (15 * d + 1) - 1 + 16 ^ (15 * d) * 16 * (16 ^ 15 - 1) := by
      rw [show 16 ^ (15 * d + 1 + 15) = 16 ^ (15 * d + 1) * 16 ^ 15 by group]
      omega

    -- prove equation both sides divisible by 5, use h2 h3 h4
    have h6 : (16 ^ (15 * d + 1 + 15) - 1) / 5 = (16 ^ (15 * d + 1) - 1) / 5 + (16 ^ (15 * d) * 16 * (16 ^ 15 - 1)) / 5 := by
      rw [h5]
      calc
        _ = (16 ^ (15 * d + 1) - 1) / 5 + (16 ^ (15 * d) * 16 * (16 ^ 15 - 1)) / 5 := by omega
        _ = (16 ^ (15 * d + 1) - 1) / 5 + (16 ^ (15 * d) * 16 * (16 ^ 15 - 1)) / 5 := by omega

    -- change 15 * (d + 1) + 1 = 15 * d + 1 + 15, for match with left side of h6
    rw [show 15 * (d + 1) + 1 = 15 * d + 1 + 15 by group ]
    rw [h6, Nat.add_mod, h1]
    omega


/-- the odd digit equal to 0, so the largest positive integer N = d 0 * (-4) ^ 0 + d 2 * (-4) ^ 2 +
d 4 * (-4) ^ 4 + ..., N = d 0 * 4 ^ 0 + d 2 * 4 ^ 2 + d 4 * 4 ^ 4 + ... -/
theorem Number_Theory_635408 (k N a : ℕ) (hka : k = 30 * a + 1) (hk_odd : Odd k)
    (hk1 : (k + 1) / 2 % 5 = 1) (hk2 : k % 6 = 1) (hN : N = 3 * (∑ i ∈ range ((k + 1) / 2), (4^2)^i)) : (16 ^ ((k + 1) / 2) - 1) / 5 % 210 = 3 := by

  -- given (k + 1) / 2 % 5 = 1and k % 6 = 1, use Chinese Remainder Theorem to prove k % 30 = 1
  have k_range : k % 30 = 1 := by omega

  -- k + 1 is Even, so (k + 1) can be divided by 2
  have h_k_add_one_even : Even (k + 1) := by field_simp

  -- calculate ∑ i ∈ range ((k + 1) / 2), (4^2)^i
  have k_digit_num : ∑ i ∈ range ((k + 1) / 2), (4^2)^i = (16 ^ ((k + 1) / 2) - 1) / (15 : ℚ) := by
    -- use geometric progression to prove
    induction' (k + 1) / 2 with d hd
    .
      -- base case
      group
    .
      -- inductive step
      rw [sum_range_succ]
      rw [hd]
      ring


  -- use the k_digit_num to prove N
  rw [hka, show (30 * a + 1 + 1) / 2 = 15 * a + 1 by omega]

  exact N_mod_210 a