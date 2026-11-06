import Mathlib
/- For each positive integer $n$ and non-negative integer $k$, define $W(n, k)$ recursively by $W(n, 0) = n^n$ and $W(n, k+1) = W(W(n, k), k)$ for $k \ge 0$.
Let $m$ be a positive integer such that $m \ge 3$ and $m$ is a multiple of $5$. Show that for any non-negative integer $k_0$, $W(m, k_0) \pmod{125} = 0$. -/
theorem algebra_636197 (m : ℕ) (W : ℕ × ℕ → ℕ) (h1 : ∀ n : ℕ, W (n + 1, 0) = (n + 1) ^ (n + 1)) (hW : ∀ n k : ℕ, W (n + 1, k + 1) = W (W (n + 1, k), k)) (hm : m ≥ 3 ∧ 5 ∣ m) : ∀ k : ℕ, W (m, k) ≡ 0 [MOD 125]:= by
  -- First, prove that W(n+1, k) > 0 for all k and n
  have h2 : ∀ k n : ℕ, W (n + 1, k) > 0:= by
    intro k
    induction k with
    | zero =>
      -- Base case: W(n+1, 0) = (n+1)^(n+1) > 0
      intro n
      rw [h1 n]
      positivity
    | succ k ih =>
      -- Inductive step: W(n+1, k+1) = W(W(n+1, k), k) > 0 by induction hypothesis
      intro n
      rw [hW n k]
      have g:= ih n
      specialize ih (W (n + 1, k) - 1)
      rw [show W (n + 1, k) - 1 + 1 = W (n + 1, k) by omega] at ih
      exact ih
  -- Prove that W(5m+5, k) is divisible by 125 for all k and m
  have h3 : ∀ k m : ℕ, 125 ∣ W (5 * m + 5, k):= by
    intro k
    induction k with
    | zero =>
      -- Base case: W(5m+5, 0) = (5m+5)^(5m+5) = 5^(5m+5) * (m+1)^(5m+5)
      intro m
      rw [h1 (5 * m + 4)]
      rw [show 5 * m + 4 + 1 = 5 * (m + 1) by omega]
      rw [show (5 * (m + 1)) ^ (5 * (m + 1)) = 5 ^ (5 * (m + 1)) * (m + 1) ^ (5 * (m + 1)) by exact Nat.mul_pow 5 (m + 1) (5 * (m + 1))]
      -- Show that 125 divides 5^(5m+5)
      suffices 125 ∣ 5 ^ (5 * (m + 1)) by rcases this with ⟨r, hr⟩ ; use r * (m + 1) ^ (5 * (m + 1)) ; rw [hr] ; ring
      rw [show 5 ^ (5 * (m + 1)) = (5 ^ 5) ^ (m + 1) by exact Nat.pow_mul 5 5 (m + 1)]
      simp
      -- 125 = 5^3 divides 3125 = 5^5
      have g : 125 ∣ 3125:= by omega
      have g1 : 3125 ∣ 3125 ^ (m + 1):= by use 3125 ^ m ; ring_nf
      exact Nat.dvd_trans g g1
    | succ k ih =>
      -- Inductive step: W(5m+5, k+1) = W(W(5m+5, k), k)
      intro m
      rw [hW (5 * m + 4) k]
      rw [show 5 * m + 4 + 1 = 5 * m + 5 by omega]
      have g:= ih m
      -- By induction hypothesis, W(5m+5, k) is divisible by 5
      replace g : 5 ∣ W (5 * m + 5, k):= by omega
      rcases g with ⟨r, hr⟩
      specialize h2 k (5 * m + 4)
      rw [show 5 * m + 4 + 1 = 5 * m + 5 by omega] at h2
      replace h2 : r > 0:= by omega
      -- Set t = r - 1, so r = t + 1
      set t:= r - 1 with ht
      clear_value t
      replace ht : r = t + 1:= by omega
      subst r
      rw [hr]
      rw [show 5 * (t + 1) = 5 * t + 5 by omega]
      -- Apply induction hypothesis to t
      exact ih t
  -- Extract the conditions from hm: m ≥ 3 and 5 divides m
  rcases hm with ⟨hm1, hm2⟩
  rcases hm2 with ⟨r, hr⟩
  replace hm1 : r > 0:= by omega
  -- Set t = r - 1, so r = t + 1
  set t:= r - 1 with ht
  clear_value t
  replace ht : r = t + 1:= by omega
  subst r
  rw [hr]
  rw [show 5 * (t + 1) = 5 * t + 5 by omega]
  -- Apply the result h3 to show W(m, k) ≡ 0 (mod 125)
  intro k
  specialize h3 k t
  exact Nat.modEq_zero_iff_dvd.mpr h3
