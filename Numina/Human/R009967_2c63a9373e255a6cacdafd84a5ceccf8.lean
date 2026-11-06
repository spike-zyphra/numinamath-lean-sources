import Mathlib

/- Let $f$ be a strictly increasing function defined in the set of natural numbers satisfying the conditions $f(2)=a>2$ and $f(m n)=f(m) f(n)$ for all natural numbers $m$ and $n$. Determine the smallest possible value of $a$. -/
theorem algebra_607922 : IsLeast {a : ℕ | ∃ f : ℕ → ℕ, StrictMono f ∧ f 2 = a ∧ a > 2 ∧ ∀ m n, f (m * n) = f m * f n} 4 := by
  unfold IsLeast lowerBounds
  simp
  constructor
  -- show $f(x) = x^2$ is a solution
  . use (fun n => n ^ 2)
    simp
    constructor
    . exact Nat.pow_left_strictMono (by norm_num)
    . intro x y
      ring
  -- show $a = 4$ is a lower bound
  . intro a f hf_mono hf2 a_min hf
    -- Prove it by contradiction, so we will find a contradiction when $a = 3$
    by_contra a_max
    simp at a_max
    have ha := eq_of_le_of_le (Nat.succ_le_of_lt a_min) (Nat.le_pred_of_lt a_max)
    simp at ha
    rw [<-ha] at hf2
    clear a_min a_max ha a

    -- set $m = 1$ and $n = 2$ in `hf`, we get $f(1)=1$
    have f1_eq_1 : f 1 = 1 := by
      have h := hf 1 2
      simp [hf2] at h
      exact h

    -- using induction to prove $f(n^k) = f(n)^k$
    have f_pow_eq_pow {n k : ℕ}: f (n ^ k) = f n ^ k := by
      induction k with
      | zero => simp [f1_eq_1]
      | succ n' ih =>
        rw [Nat.pow_succ, hf, ih, Nat.pow_succ]

    -- prove $5 < f(3)$ by $5 ^ 4 < 3 ^ 6 = f(2) ^ 6 = f(2^6) < f(3 ^ 4) = f(3) ^ 4$
    have h1 : 5 ^ 4 < (f 3) ^ 4 := by
      rw [<-f_pow_eq_pow]
      have : 2 ^ 6 < 3 ^ 4 := by simp
      apply lt_trans' (hf_mono this)
      rw [f_pow_eq_pow, hf2]
      simp
    rw [Nat.pow_lt_pow_iff_left (by norm_num)] at h1

    -- prove $f(3) < 6$ by $f(3) ^ 8 = f(3^8) < f(2^13) = f(2) ^ 13 = 3 ^ 13 < 6 ^ 8$
    have h2 : (f 3) ^ 8 < 6 ^ 8 := by
      rw [<-f_pow_eq_pow]
      have : 3 ^ 8 < 2 ^ 13 := by simp
      apply lt_trans (hf_mono this)
      rw [f_pow_eq_pow, hf2]
      simp
    rw [Nat.pow_lt_pow_iff_left (by norm_num)] at h2
    -- find a contradiction from $5 < f(3) \and f(3) < 6$
    linarith
