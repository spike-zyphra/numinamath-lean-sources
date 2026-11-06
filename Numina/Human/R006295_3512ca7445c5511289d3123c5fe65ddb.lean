import Mathlib
/- Let $n$ be a positive integer and $k$ be any integer. Define $m = kn+1$.
Show that the expression $\frac{(n-1)m^n - n m^{n-1} + 1}{n^2}$ is an integer. -/
theorem number_theory_635623 (n : ℕ) (k m : ℤ) (hn : n > 0) (hm : m = k * n + 1) : (↑n : ℤ) ^ 2 ∣ (n - 1) * m ^ n - n * m ^ (n - 1) + 1:= by
  -- Substitute the value of m
  subst m

  -- Prove that (kn+1)^t ≡ tkn + 1 (mod n^2) for all natural numbers t
  have h1 : ∀ t : ℕ, (k * n + 1) ^ t ≡ t * k * n + 1 [ZMOD n ^ 2]:= by
    intro t
    induction t with
    -- Base case: when t = 0
    | zero =>
      simp
    -- Inductive step: prove for t + 1 assuming it holds for t
    | succ t ih =>
      -- Rewrite (kn+1)^(t+1) as (kn+1)^t * (kn+1)
      rw [show (k * ↑n + 1) ^ (t + 1) = (k * ↑n + 1) ^ t * (k * ↑n + 1) by ring]
      -- Apply inductive hypothesis with multiplication
      replace ih : (k * ↑n + 1) ^ t * (k * ↑n + 1) ≡ (↑t * k * ↑n + 1) * (k * ↑n + 1) [ZMOD ↑n ^ 2]:= by exact Int.ModEq.mul ih rfl
      simp
      -- Algebraic manipulation to complete the proof
      rw [show (↑t * k * ↑n + 1) * (k * ↑n + 1) = t * k ^ 2 * n ^ 2 + (↑t + 1) * k * ↑n + 1 by ring] at ih
      suffices t * k ^ 2 * n ^ 2 + (↑t + 1) * k * ↑n + 1 ≡ (↑t + 1) * k * ↑n + 1 [ZMOD ↑n ^ 2] by exact Int.ModEq.trans ih this
      set s:= (↑t + 1) * k * ↑n + 1 with hs
      clear_value s
      rw [show ↑t * k ^ 2 * ↑n ^ 2 + (↑t + 1) * k * ↑n + 1 = t * k ^ 2 * n ^ 2 + s by subst s ; ring]
      suffices (n : ℤ) ^ 2 ∣ ↑t * k ^ 2 * ↑n ^ 2 + s - s by exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) this)
      ring_nf
      use t * k ^ 2
      ring

  -- Apply the congruence for t = n-1 and t = n
  have h2:= h1 (n - 1)
  replace h1:= h1 n

  -- Multiply the congruences by appropriate factors
  replace h1 : (n - 1) * (k * ↑n + 1) ^ n ≡ (n - 1) * (↑n * k * ↑n + 1) [ZMOD ↑n ^ 2]:= by exact Int.ModEq.mul_left (↑n - 1) h1
  field_simp at h2
  replace h2 : n * (k * ↑n + 1) ^ (n - 1) ≡ n * ((n - 1) * k * ↑n + 1) [ZMOD ↑n ^ 2]:= by exact Int.ModEq.mul_left (↑n) h2

  -- Combine the congruences to complete the proof
  replace h1:= Int.ModEq.sub h1 h2
  replace h1 : (↑n - 1) * (k * ↑n + 1) ^ n - ↑n * (k * ↑n + 1) ^ (n - 1) + 1 ≡ (↑n - 1) * (↑n * k * ↑n + 1) - ↑n * ((↑n - 1) * k * ↑n + 1) + 1 [ZMOD ↑n ^ 2]:= by exact Int.ModEq.add h1 rfl
  rw [show (↑n - 1) * (↑n * k * ↑n + 1) - ↑n * ((↑n - 1) * k * ↑n + 1) + 1 = 0 by ring_nf] at h1
  exact Int.dvd_of_emod_eq_zero h1
