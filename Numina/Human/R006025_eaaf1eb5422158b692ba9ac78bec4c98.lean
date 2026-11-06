import Mathlib

/-Given are real numbers $x, y$. For any pair of real numbers $a_{0}, a_{1}$, define a sequence by $a_{n+2}=x a_{n+1}+y a_{n}$ for $n \geq 0$. Suppose that there exists a fixed nonnegative integer $m$ such that, for every choice of $a_{0}$ and $a_{1}$, the numbers $a_{m}, a_{m+1}, a_{m+3}$, in this order, form an arithmetic progression. Find all possible values of $y$.-/
theorem algebra_611176 (x y : ℝ) : (∃ m : ℕ, ∀ a : ℕ → ℝ,
  (∀ n, a (n + 2) = x * a (n + 1) + y * a n) → a m + a (m + 3) = 2 * a (m + 1)) ↔
  (x + x ^ 4 = 2 * x ^ 2 ∧ y = 0) ∨ (1 + x * y = 0 ∧ (y = 1 ∨
  y = (1 - √5) / 2 ∨ y = (1 + √5) / 2)) := by
-- Split "iff"
  constructor
  -- If $y$ is $0$, we only need to show $x+x^4=2*x^2$
  · rintro ⟨m, hm⟩; by_cases hy : y = 0
    -- Define $a$ to be the geometric sequence $1$, $x$, $x^2$...
    · left; simp [hy] at hm; let a : ℕ → ℝ := fun i => by induction i with
      | zero => exact 1
      | succ i an => exact x * an
      have ha : ∀ (n : ℕ), a n = x ^ n := by
        intro n; induction n with
        | zero => simp [a]
        | succ n ihn =>
          have : ∀ n, a (n + 1) = x * a n := by simp [a]
          rw [this, ihn]; ring
    -- Specialize `hm` to $a$ and simplify it, the goal follows
      specialize hm a (by simp [a]); simp [ha] at hm
      by_cases hx : x = 0; simp [hx]; exact hy
      rw [pow_add, pow_add, pow_one, ← mul_one_add] at hm
      rw [show 2*(x^m*x) = x^m*(2*x) by ring, mul_right_inj'] at hm
      constructor
      · rw [pow_two, ← mul_assoc, ← hm]; ring
      exact hy; positivity
  -- If $y$ is not $0$, show that $a_m$ and $a_(m+1)$ can take arbitrary values $p$ and $q$
    have hm' : ∀ p q : ℝ, ∃ a : ℕ → ℝ, (∀ (n : ℕ), a (n + 2) = x * a (n + 1) + y * a n) ∧
    a m = p ∧ a (m + 1) = q := by
    -- Generalize $m$ to any natural number $n$, then apply induction on $n$
      generalize m = n; induction n with
      | zero =>
      -- The base case can be shown by defining a sequence $a$ with $a_0=p$ and $a_1=q$ via `Nat.twoStepInduction`
        intro p q; rw [zero_add]
        let a : ℕ → ℝ := fun i => by induction i using Nat.twoStepInduction with
        | zero => exact p
        | one => exact q
        | more i an ans => exact x * ans + y * an
        use a; simp [a, Nat.twoStepInduction]
      -- The induction step can be done by getting a sequence $a$ with $a_n=(q-x*p)/y$ and $a_(n+1)=p$ from induction hypothesis
      | succ n ihn =>
        intro p q; rw [show n+1+1 = n+2 by ring]
        specialize ihn ((q-x*p)/y) p; rcases ihn with ⟨a, ⟨ha, an, ans⟩⟩
        use a; split_ands; exact ha; exact ans
        rw [ha, an, ans]; field_simp
  -- Substitute $p=0$ and $q=1$ in `hm'` to get a sequence $a$, then apply `hm` to $a$ and simplify it to an equation of $x$ and $y$
    obtain ⟨a, ⟨ha, an, ans⟩⟩ := hm' 0 1
    have ham := hm a ha; rw [show m+3 = m+1+2 by ring, ha] at ham
    rw [show m+1+1 = m+2 by ring, ha, an, ans, ← sub_eq_zero] at ham
    norm_num at ham
  -- Substitute $p=1$ and $q=0$ in `hm'` to get a sequence $a'$, then apply `hm` to $a'$ and simplify it to an equation of $x$ and $y$
    obtain ⟨a', ⟨ha', a'n, a'ns⟩⟩ := hm' 1 0
    have ha'm := hm a' ha'; rw [show m+3 = m+1+2 by ring, ha'] at ha'm
    rw [show m+1+1 = m+2 by ring, ha', a'n, a'ns, ← sub_eq_zero] at ha'm
    norm_num at ha'm
  -- Solve for $x$ and $y$ from the two equations `ham` and `ha'm`
    apply_fun fun t => y^2 * t at ham
    rw [mul_zero, show y^2*(x*x+y-2) = y^3-2*y^2+(x*y)^2 by ring] at ham
    rw [← neg_eq_iff_add_eq_zero] at ha'm; rw [← ha'm] at ham
    norm_num at ham
    simp [show y^3-2*y^2+1 = (y-1)*(y^2-y-1) by ring] at ham
    rcases ham with ham|ham
    · right; constructor; linarith
      left; linarith
    right; constructor; linarith
    right; rw [show y^2-y-1 = 1*(y*y)+-1*y+-1 by ring] at ham
    have : discrim 1 (-1) (-1) = √5 * √5 := by rw [discrim]; norm_num
    rw [quadratic_eq_zero_iff (show (1:ℝ)≠0 by norm_num) this, or_comm] at ham
    rw [neg_neg, mul_one] at ham; exact ham
-- Conversely, we can check that if $x$ and $y$ are of the given values, the required condition holds
  intro hy; rcases hy with ⟨hx, hy⟩|⟨hx, hy|hy|hy⟩
  · simp [hy]; use 2; intro a ha; simp [ha]
    rw [show 2*(x*(x*a 1)) = 2*x^2*a 1 by ring, ← hx]; ring
  · simp [hy] at *; rw [← neg_eq_iff_add_eq_zero] at hx
    simp [← hx]; use 1; intro a ha; simp [ha]; ring
  · use 0; intro a ha; simp [ha]; rw [← sub_eq_zero]; ring_nf
    rw [← neg_eq_iff_add_eq_zero] at hx; rw [mul_assoc, ← hx]; ring_nf
    rw [← div_eq_iff] at hx; rw [← hx, hy]
    have : (1 - √5) ^ 2 ≠ 0 := by
      simp; rw [sub_eq_zero, ← pow_left_inj₀ (by positivity) (by positivity) (show 2≠0 by simp)]
      simp [Real.sq_sqrt]
    field_simp; ring_nf; have : √5 ^ 3 = 5 * √5 := by
      rw [← pow_left_inj₀ (by positivity) (by positivity) (show 2≠0 by simp)]
      rw [mul_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]; norm_num; ring
    intro h; simp [h] at hx
  use 0; intro a ha; simp [ha]; rw [← sub_eq_zero]; ring_nf
  rw [← neg_eq_iff_add_eq_zero] at hx; rw [mul_assoc, ← hx]; ring_nf
  rw [← div_eq_iff] at hx; rw [← hx, hy]
  have : (1 + √5) ^ 2 ≠ 0 := by positivity
  field_simp; ring_nf; have : √5 ^ 3 = 5 * √5 := by
    rw [← pow_left_inj₀ (by positivity) (by positivity) (show 2≠0 by simp)]
    rw [mul_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [this]; norm_num; ring
  intro h; simp [h] at hx