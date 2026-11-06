import Mathlib

/-
Let  $f$  be a function on non-negative integers defined as follows   $$ f(2n)=f(f(n))~~~\text{and}~~~f(2n+1)=f(2n)+1 $$

**(a)** If  $f(0)=0$  , find  $f(n)$  for every  $n$ .
-/
theorem number_theory_8719_a
    (f : ℕ → ℕ)
    (h₀ : ∀ n, f (2 * n) = f (f n))
    (h₁ : ∀ n, f (2 * n + 1) = f (2 * n) + 1) :
    (f 0 = 0) ↔ ((f 0 = 0 ∧ f 1 = 1 ∧ (∀ x > 1, Even x → f x = 1) ∧ (∀ x > 1, Odd x → f x = 2))) := by
  constructor
  . intro h_f0

    -- since $f(0)=0$,  by setting  $n=1$, we get  $f(1)=1$ and $f(2)=f(f(1))=f(1)=1$.
    have r_f1 : f 1 = 1 := by
      simp [h₁ 0, h_f0]
    have r_f2 : f 2 = 1 := by
      simp [h₀ 1, r_f1]

    -- for all $x ≠ 0$, we have $f (x) = 1 \or f (x) = 2$, by induction.
    have r_1or2 : ∀ x > 0, f x = 1 ∨ f x = 2 := by
      intro x
      induction' x using Nat.strong_induction_on with x ih
      cases x
      case zero =>
        intro h
        contradiction
      case succ x =>
        induction x with
        | zero => simp [r_f1, r_f2]
        | succ x _ =>
          rcases x.even_or_odd with hx | hx
          . obtain ⟨k, hk⟩ := hx
            have : f (x + 1 + 1) = 1 := by
              rw [show x + 1 + 1 = 2 * (k + 1) by rw [hk]; ring, h₀]
              rcases ih (k + 1) (by linarith) (by linarith) with h | h
              . rw [h, r_f1]
              . rw [h, r_f2]
            simp [this]
          . obtain ⟨k, hk⟩ := hx
            have : f (x + 1 + 1) = 2 := by
              rw [show x + 1 + 1 = 2 * (k + 1) + 1 by rw [hk]; ring, h₁, h₀]
              rcases ih (k + 1) (by linarith) (by linarith) with h | h
              . rw [h, r_f1]
              . rw [h, r_f2]
            simp [this]

    -- then for all $m > 0$, we have $f (2m) = f(f(m)) = f(1) = 1$ and $f(2m+1) = f(2m) + 1 = 1 + 1 = 2$.
    have r_gen: ∀ m > 0, f (2 * m) = 1 ∧ f (2 * m + 1) = 2 := by
      intro m hm
      constructor
      . rw [h₀]
        rcases r_1or2 m hm with h | h
        <;> simp [h, r_f1, r_f2]
      . rw [h₁, h₀]
        rcases r_1or2 m hm with h | h
        <;> simp [h, r_f1, r_f2]

    -- conclusion
    have r_feven : ∀ x > 1, Even x → f x = 1 := by
      intro x h_xgt1 h_xeven
      obtain ⟨m, hm⟩ := h_xeven
      have r_mpos : 0 < m := by linarith
      rw [hm, ← two_mul]
      exact (r_gen m r_mpos).left

    have r_fodd : ∀ x > 1, Odd x → f x = 2 := by
      intro x h_xgt1 h_xodd
      obtain ⟨m, hm⟩ := h_xodd
      have r_mpos : 0 < m := by linarith
      rw [hm]
      exact (r_gen m r_mpos).right

    exact ⟨h_f0, r_f1, r_feven, r_fodd⟩

  . intro ⟨h1, _⟩
    exact h1

/-
Let  $f$  be a function on non-negative integers defined as follows   $$ f(2n)=f(f(n))~~~\text{and}~~~f(2n+1)=f(2n)+1 $$

**(b)** Show that  $f(0)$  cannot equal  $1$ .
-/
theorem number_theory_8719_b
    (f : ℕ → ℕ)
    (h₀ : ∀ n, f (2 * n) = f (f n))
    (h₁ : ∀ n, f (2 * n + 1) = f (2 * n) + 1) :
    f 0 ≠ 1 := by

  -- FTSOC, we get 2 = 1, contradiction
  by_contra h_f0
  specialize h₀ 0
  specialize h₁ 0

  rw [mul_zero, h_f0] at h₀
  rw [mul_zero, zero_add, h_f0, ← h₀] at h₁
  contradiction

/-
Let  $f$  be a function on non-negative integers defined as follows   $$ f(2n)=f(f(n))~~~\text{and}~~~f(2n+1)=f(2n)+1 $$

**(c)** For what non-negative integers  $k$  (if any) can  $f(0)$  equal  $2^k$​  ?
-/
theorem number_theory_8719_c
    (f : ℕ → ℕ)
    (h₀ : ∀ n, f (2 * n) = f (f n))
    (h₁ : ∀ n, f (2 * n + 1) = f (2 * n) + 1) :
    ∀ k : ℕ, f 0 ≠ 2 ^ k := by

  -- FTSOC, we have $f 0 = 2 ^ k$ for some $k$
  by_contra! h
  obtain ⟨k, h_f0⟩ := h

  rcases ne_or_eq k 0 with hk | hk

  -- $k \ne 0$
  . have r_f1 : f 1 = 2 ^ k + 1 := by
      simp [h₁ 0, h_f0]

    -- $f(2 ^ k) = f(f(0)) = f(2 * 0) = f(0) = 2 ^ k$
    have r_f2pk : f (2 ^ k) = 2 ^ k := by
      simp [← h_f0, ← h₀]

    -- for all $n$, $f(2 ^ n) = 2 ^ k + 1$ by induction.
    have r_f2pn : ∀ n : ℕ, f (2 ^ n) = 2 ^ k + 1 := by
      intro n
      induction n with
      | zero => simp [r_f1]
      | succ n ih =>
        conv =>
          lhs
          rw [pow_add, pow_one, mul_comm, h₀, ih,
              ← mul_pow_sub_one hk 2, h₁, mul_pow_sub_one hk 2, r_f2pk]

    -- $2 ^ k + 1 = 2 ^ k$ , contradicion
    simp_all

  -- $k = 0$, use the result of subproblem (b)
  . rw [hk, pow_zero] at h_f0
    exact number_theory_8719_b f h₀ h₁ h_f0
