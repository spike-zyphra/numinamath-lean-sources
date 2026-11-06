import Mathlib

/- 5. A5 (POL) Let $f(x)=\frac{x^{2}+1}{2 x}$ for $x \neq 0$. Define $f^{(0)}(x)=x$ and $f^{(n)}(x)=$ $f\left(f^{(n-1)}(x)\right)$ for all positive integers $n$ and $x \neq 0$. Prove that for all nonnegative integers $n$ and $x \neq-1,0$, or 1 ,  $$ \frac{f^{(n)}(x)}{f^{(n+1)}(x)}=1+\frac{1}{f\left(\left(\frac{x+1}{x-1}\right)^{2^{n}}\right)} $$ -/
theorem algebra_24574 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 0 → f x = (x ^ 2 + 1) / (2 * x)):
  ∀ n : ℕ, ∀ x, x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 →
  (f^[n] x) / (f^[n + 1] x) = 1 + 1 / f (((x + 1) / (x - 1)) ^ (2 ^ n)) := by
  -- if x is not -1, 0, 1, then f(x) is not either.
  have hfne {x:ℝ} (hx: x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1):
    f x ≠ -1 ∧ f x ≠ 0 ∧ f x ≠ 1 := by
    rw [hf x hx.right.left]
    have: 2*x ≠ 0 := by simp [hx.right.left]
    field_simp [this]
    split_ands <;> rintro heq
    · replace heq: (x+1)^2 = 0 := by linarith only [heq]
      simp only [ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff] at heq
      absurd hx.left; linarith only [heq]
    · have: x^2+1 > 0 := by linarith only [sq_nonneg x]
      simp [heq] at this
    · replace heq: (x-1)^2 = 0 := by linarith only [heq]
      simp only [ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff] at heq
      absurd hx.right.right
      linarith only [heq]

  have hfne' {x:ℝ} (hx: x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1):
    ∀n, f^[n] x ≠ -1 ∧ f^[n] x ≠ 0 ∧ f^[n] x ≠ 1 := by
    intro n
    induction' n with n ih
    · simp [hx]
    · rw [Function.iterate_succ', Function.comp_apply]
      apply hfne ih

  -- define p0 = x, q0 = 1, and p_{n+1} = p_n^2 + q_n^2, q_{n+1} = 2p_n q_n.
  let P (x:ℝ): ℕ → ℝ × ℝ := fun n =>
    Nat.recOn n ⟨x,1⟩
      fun n p => ⟨p.1^2+p.2^2, 2*p.1*p.2⟩

  -- we claim f^(n) (x) = p_n / q_n
  have hf1 {x:ℝ} (hx: x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1):
    ∀n, f^[n] x = (P x n).1 / (P x n).2 := by
    intro n
    induction' n with n ih
    · simp [P]
    · dsimp only [P]
      specialize hfne' hx n
      rw [Function.iterate_succ', Function.comp_apply,
      hf _ hfne'.right.left]
      have h1: 2 * f^[n] x ≠ 0 := by simp [hfne'.right.left]
      have h2: (P x n).2 ≠ 0 := by
        by_contra!
        simp only [this, div_zero] at ih
        simp [ih] at hfne'
      have h3: (P x n).1 ≠ 0 := by
        by_contra!
        simp only [this, zero_div] at ih
        simp [ih] at hfne'
      field_simp [h1]
      rw [ih]
      field_simp [h2, h3]
      ring

  -- and we claim p_n(x) = ((x+1)^(2^n) + (x-1)^(2^n)) / 2,
  -- q_n(x) = ((x+1)^(2^n) - (x-1)^(2^n)) / 2
  have hpq {x:ℝ} (n:ℕ) (hx: x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1):
    (P x n).1 = ((x+1)^2^n + (x-1)^2^n) / 2 ∧
    (P x n).2 = ((x+1)^2^n - (x-1)^2^n) / 2 := by
    induction' n with n ih
    · simp [P]
    · dsimp only [P]
      rw [ih.left, ih.right]
      ring_nf; trivial

  -- express f^(n) (x) / f^(n+1) (x) in terms of p_n, q_n
  intro n x hx
  have f_of_p: f^[n] x / f^[n+1] x =
    (2 * (P x n).1^2) / ((P x n).1^2 + (P x n).2^2) := by
    rw [hf1 hx n , hf1 hx (n+1)]
    dsimp only [P]
    rw [div_div_eq_mul_div]
    congr 1
    have: (P x n).2 ≠ 0 := by
      specialize hf1 hx n
      by_contra!
      simp only [this, div_zero] at hf1
      specialize hfne' hx n
      simp [hf1] at hfne'
    field_simp [this]
    ring

  -- express p,q in terms of x, simplify 2p_n / (p_n^2 + q_n^2)
  have: (2 * (P x n).1^2) / ((P x n).1^2 + (P x n).2^2) =
    1 + 2 * ((x+1)/(x-1))^2^n / (1 + (((x+1)/(x-1))^2^n)^2) := by
    specialize hpq n hx
    have h1: (2 * (P x n).1^2) / ((P x n).1^2 + (P x n).2^2) =
      2 * (2 * (P x n).1^2) / (2 * ((P x n).1^2 + (P x n).2^2)) := by
      by_cases h: ((P x n).1^2 + (P x n).2^2) = 0
      · simp [h]
      · field_simp [h]
        ring
    have h2: 2 * (2 * (P x n).1^2) = ((x+1)^2^n + (x-1)^2^n)^2 := by
      rw [hpq.left, div_pow, ← mul_assoc]
      norm_num
      rw [mul_div_cancel₀ _ (by norm_num)]
    have h3: 2 * ((P x n).1^2 + (P x n).2^2) =
      ((x+1)^2^n)^2 + ((x-1)^2^n)^2 := by
      rw [hpq.left, hpq.right]
      simp only [div_pow]
      rw [add_sq, sub_sq]
      ring
    have h4 {a b: ℝ} (hh1: a^2 + b^2 ≠ 0) (hh2: b ≠ 0):
      (a+b)^2 / (a^2 + b^2) = 1 + (2*(a/b)) / (1 + (a/b)^2) := by
      rw [show (a+b)^2 = 2*a*b + (a^2+b^2) by ring]
      rw [← div_add_one hh1, add_comm _ 1]
      congr 1
      have: 1 + (a/b)^2 ≠ 0 := by
        have: a^2 + b^2 = b^2 * (1 + (a/b)^2) := by
          field_simp [hh2]
          ring
        rw [this] at hh1
        exact right_ne_zero_of_mul hh1
      field_simp [this, hh1, hh2]
      ring
    have h5: (x-1)^2^n ≠ 0 := by
      by_contra!
      simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
      false_and, not_false_eq_true, pow_eq_zero_iff] at this
      absurd hx.right.right
      linarith only [this]
    have h6: ((x+1)^2^n)^2 + ((x-1)^2^n)^2 > 0 := by
      suffices ((x-1)^2^n)^2 > 0 by
        linarith only [sq_nonneg ((x+1)^2^n), this]
      exact pow_two_pos_of_ne_zero h5
    rw [h1, h2, h3, h4 h6.ne' h5, ← div_pow]
  nth_rw 2 [add_comm 1 _] at this

  -- and it is exactly 1 + 1 / f(...)
  rw [f_of_p, this, hf, one_div_div]
  simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and,
  not_false_eq_true, pow_eq_zero_iff, div_eq_zero_iff, not_or, P]
  constructor <;> rintro hh
  · absurd hx.left; linarith only [hh]
  · absurd hx.right.right; linarith only [hh]