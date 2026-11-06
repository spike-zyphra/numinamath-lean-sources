import Mathlib

/- Find all increasing functions $f: \mathbb{R} \rightarrow \mathbb{R}$, such that $f(1)=1$ and, for all $x, y \in \mathbb{R}, f(x+y)=f(x)+f(y)$. -/
theorem algebra_150253 (f : ℝ → ℝ) (h₀ : Monotone f) (h₁ : f 1 = 1)
    (h₂ : ∀ x y, f (x + y) = f x + f y) : ∀ x, f x = x := by
  -- We will show that f is the identity function. First we show
  -- by induction that f (n * x) = n * f x for all n : ℕ and x : ℝ.
  have f_zero : f 0 = 0 := by
    have : f 0 + f 0 = f 0 + 0 := by rw [← h₂]; simp
    exact add_left_cancel this

  have f_neg : ∀ x, f (-x) = -f x := by
    intro x
    rw [← add_eq_zero_iff_eq_neg', ← h₂]
    simp
    exact f_zero

  have f_mul_nat (n : ℕ) (x : ℝ) : f (n * x) = n * f x := by
    induction n with
    | zero =>
      simp
      exact f_zero
    | succ n ih =>
      push_cast
      rw [add_mul, add_mul, h₂, ih]
      simp

  -- This implies that f is the identity function on the natural numbers,
  -- the integers, and finally the rational numbers.
  have f_nat : ∀ n : ℕ, f n = n := by
    intro n
    rw [show (n : ℝ) = n * 1 by simp, f_mul_nat n 1, h₁]

  have f_int : ∀ n : ℤ, f n = n := by
    intro n
    cases n with
    | ofNat n => exact f_nat n
    | negSucc n =>
      push_cast
      rw [f_neg, h₂, h₁, f_nat]

  have f_rat : ∀ x : ℚ, f x = x := by
    intro x
    cases x with
    | mk' n d h =>
      rw [Rat.mk_eq_divInt]
      push_cast
      rw [eq_div_iff_mul_eq (by simp [h]), mul_comm]
      rw [← f_mul_nat, mul_div_cancel₀ _ (by simp [h])]
      exact f_int n

  -- Finally we show that f is the identity function on the reals.
  -- If f x < x, then there is a rational number q such that f x < q < x.
  intro x
  rcases lt_trichotomy (f x) x with (hx | hx | hx)
  . exfalso
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx
    have : f q ≤ f x := h₀ (by linarith)
    rw [f_rat q] at this
    linarith
  . exact hx
  . exfalso
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx
    have : f x ≤ f q := h₀ (by linarith)
    rw [f_rat q] at this
    linarith